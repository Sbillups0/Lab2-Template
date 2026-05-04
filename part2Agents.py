from model import (
    Location,
    Wizard,
    IceStone,
    FireStone,
    WizardMoves,
    GameAction,
    GameState,
    Wall,
    WizardSpells, NeutralStone,
)
from agents import WizardAgent

import z3
from z3 import (Solver, Bool, Bools, Int, Ints, Or, Not, And, Implies, Distinct, If)

# Shared Helper Functions
def build_maysu_solver(state: GameState, fire_locations: list, ice_locations: list):
    #Returns (solver, hedge, vedge, R, C, wizard_location)
    R, C = state.grid_size # Number of rows and columns in the grid
    wizard_location = state.active_entity_location
    s = Solver()
    #Edge variables (hedge/vedge) represent whether the path goes through the edge between two cells horizontally or vertically
    hedge = [[Bool(f"hedge_{r}_{c}") for c in range(C-1)] for r in range(R)]
    vedge = [[Bool(f"vedge_{r}_{c}") for c in range(C)] for r in range(R-1)]

    # Convenient helper functions to access the edge variables, returning None if the edge is out of bounds
    def N(r, c):
        return vedge[r-1][c] if r > 0 else None
    def S(r, c):
        return vedge[r][c] if r < R-1 else None
    def W(r, c):
        return hedge[r][c-1] if c > 0 else None
    def E(r, c):
        return hedge[r][c] if c < C-1 else None
    
    def b(e):
        return e if e is not None else False # Treat out-of-bounds edges as False (no path)
    
    def get_edges(r, c):
        return [e for e in [N(r, c), S(r, c), W(r, c), E(r, c)] if e is not None]
    
    def degree(r, c):
        #z3 expression for number of active edges at (r, c)
        edges = get_edges(r, c)
        if not edges:
            return z3.IntVal(0)
        return z3.Sum([If(e, 1, 0) for e in edges])
    
    #Degree and wall constraints
    # Every cell is either not on path (degree 0) or fully on path (degree 2)
    # Wall cells have all incident edges forced to be False (no path can go through them)
    for r in range(R):
        for c in range(C):
            tile = state.tile_grid[r][c]
            if isinstance(tile, Wall):
                # Wall cell: no edges can be active
                for e in get_edges(r, c):
                    s.add(Not(e))
            else:
                # Non-wall cell: degree must be 0 or 2
                d = degree(r, c)
                s.add(Or(d == 0, d == 2))
    #Stone coverage constraints
    # Every stone must be visited by the path
    for loc in fire_locations + ice_locations:
        s.add(degree(loc.row, loc.col) == 2) # Stone cells must have degree 2 (must be on the path)

    # Wizard start location is also part of the loop
    s.add(degree(wizard_location.row, wizard_location.col) == 2)

    #Fire Stone constaints
    # Rule 1: path must turn at fire stone 
    # Rule 2: Each path-direction neghbour must be straight (line continues for at least one more cell beyond the turn)
    for loc in fire_locations:
        r, c = loc.row, loc.col
        n, sv, w, e = N(r, c), S(r, c), W(r, c), E(r, c)

        # Rule 1: path must turn at fire stone (cannot go straight through) (Forbid straight NS/WE)
        if n is not None and sv is not None:
            s.add(Not(And(n, sv))) # Cannot have both N and S active (no straight vertical)
        if w is not None and e is not None:
            s.add(Not(And(w, e))) # Cannot have both W and E active (no straight horizontal)
        
        # Rule 2: Each path-direction neighbor must be straight (line continues for at least one more cell beyond the turn)
        # If path goes north, then it must continue north from that neighbor (and similarly for S/W/E)
        for edge, get_fn, nr, nc in [(n, N, r-1, c), (sv, S, r+1, c), (w, W, r, c-1), (e, E, r, c+1)]:
            if edge is not None:
                cont = get_fn(nr, nc) # Edge that continues in the same direction from the neighbor cell
                if cont is not None:
                    #If this edge is used, neighbor must continue in the same direction (enforce straight line beyond the turn)
                    s.add(Implies(edge, cont))
                else:
                    # If there is no cell beyond the neighbor in this direction, then the path cannot go in this direction from the fire stone
                    s.add(Not(edge))
        
    #Ice Stone constraints
    # Rule 1: path must go straight through ice stone (cannot turn)
    # Rule 2: At least one two path-direction neighbor must turn (Both neighbors cannot be straight in the same direction)
    for loc in ice_locations:
        r, c = loc.row, loc.col
        n, sv, w, e = N(r, c), S(r, c), W(r, c), E(r, c)
        can_ns = n is not None and sv is not None
        can_we = w is not None and e is not None
        # Rule 1: path must go straight through ice stone (cannot turn) (Must go straight NS or WE)
        if can_ns and can_we:
            s.add(Or(And(n, sv, Not(And(w, e))), And(w, e, Not(And(n, sv))))) # Must go straight NS or WE (cannot turn)
        elif can_ns:
            s.add(And(n, sv)) # Must go straight NS (only possible direction)
        elif can_we:
            s.add(And(w, e)) # Must go straight WE (only possible direction)
        
        # Rule 2 NS direction
        if can_ns:
            n_nbr_cont = N(r-1, c) if r > 1 else None # Edge that continues north from the northern neighbor
            sv_nbr_cont = S(r+1, c) if r < R-2 else None # Edge that continues south from the southern neighbor
            s.add(Implies(And(n, sv), Not(And(b(n_nbr_cont), b(sv_nbr_cont))))) # If going straight NS through ice stone, neighbors cannot both continue straight (at least one must turn)
        # Rule 2 WE direction
        if can_we:
            w_nbr_cont = W(r, c-1) if c > 1 else None # Edge that continues west from the western neighbor
            e_nbr_cont = E(r, c+1) if c < C-2 else None # Edge that continues east from the eastern neighbor
            s.add(Implies(And(w, e), Not(And(b(w_nbr_cont), b(e_nbr_cont))))) # If going straight WE through ice stone, neighbors cannot both continue straight (at least one must turn)

    # Connectivity constaints (prevent disjoint loops by enforcing no small loops and that all cells are reachable from the wizard start location)
    label = [[Int(f"label_{r}_{c}") for c in range(C)] for r in range(R)]
    for r in range(R):
        for c in range(C):
            s.add(label[r][c] >= 0) # Labels must be non-negative
            s.add(label[r][c] < R*C) # Labels must be less than total number of cells
    s.add(label[wizard_location.row][wizard_location.col] == 0) # Wizard start location has label 0
    for r in range(R):
        for c in range(C):
            if Location(r, c) == wizard_location:
                continue
            in_loop = degree(r, c) == 2
            not_in_loop = degree(r, c) == 0
            # If cell is in the loop, it must have at least one neighbor in the loop with smaller label (enforce connectivity and no small loops)
            smaller_nbrs = []
            for edge, nr, nc in [(N(r, c), r-1, c), (S(r, c), r+1, c), (W(r, c), r, c-1), (E(r, c), r, c+1)]:
                if edge is not None and 0 <= nr < R and 0 <= nc < C:
                    smaller_nbrs.append(And(edge, label[nr][nc] == label[r][c] - 1)) # Neighbor is in the loop and has smaller label
            if smaller_nbrs:
                s.add(Implies(in_loop, And(label[r][c] > 0, Or(smaller_nbrs)))) # If in loop, must have a smaller labeled neighbor in the loop
            s.add(Implies(not_in_loop, label[r][c] == 0)) # If not in loop, label must be 0 (not reachable)
    return s, hedge, vedge, R, C, wizard_location

def extract_path(model, wizard_location: Location, hedge, vedge, R: int, C: int):
    #Reads the true edge variables from z3 model and builds the path from wizard_location, returning a list of WizardMoves in order to solve the puzzle
    adj: dict[Location, Location] = {
        Location(r, c): [] for r in range(R) for c in range(C) # Initialize adjacency list for each cell
    }
    for r in range(R):
        for c in range(C-1):
            if z3.is_true(model.evaluate(hedge[r][c])):
                adj[Location(r, c)].append(Location(r, c+1)) # Edge to the right
                adj[Location(r, c+1)].append(Location(r, c)) # Edge to the left
    for r in range(R-1):
        for c in range(C):
            if z3.is_true(model.evaluate(vedge[r][c])):
                adj[Location(r, c)].append(Location(r+1, c)) # Edge down
                adj[Location(r+1, c)].append(Location(r, c)) # Edge up

    # Now build the path starting from wizard_location
    path = [wizard_location]
    prev, current = None, wizard_location
    while True:
        next_cell = next(
            (nb for nb in adj[current] if nb != prev), None # Get the next cell in the path (the neighbor that is not the previous cell)
        )
        if next_cell is None or next_cell == wizard_location:
            path.append(wizard_location) # Add the starting location at the end to complete the loop
            break # Completed the loop
        path.append(next_cell)
        prev, current = current, next_cell
    #Convert consecutive locations in path to WizardMoves
    moves = []
    for i in range(len(path) - 1):
        dr = path[i+1].row - path[i].row
        dc = path[i+1].col - path[i].col
        if dr == -1 and dc == 0:
            moves.append(WizardMoves.UP)
        elif dr == 1 and dc == 0:
            moves.append(WizardMoves.DOWN)
        elif dr == 0 and dc == -1:
            moves.append(WizardMoves.LEFT)
        elif dr == 0 and dc == 1:
            moves.append(WizardMoves.RIGHT)
    return moves

class PuzzleWizard(WizardAgent):
    def __init__(self, initial_state: GameState):
        self.moves: list[WizardMoves] = self._solve(initial_state)
    def _solve(self, state: GameState) -> list[WizardMoves]:
        fire_locations = state.get_all_tile_locations(FireStone)
        ice_locations = state.get_all_tile_locations(IceStone)
        solver, hedge, vedge, R, C, wizard_location = build_maysu_solver(state, fire_locations, ice_locations)
        if solver.check() == z3.sat:
            model = solver.model()
            return extract_path(model, wizard_location, hedge, vedge, R, C)
        else:
            raise Exception("No solution found for the given puzzle")
            return []
    def react(self, state: GameState) -> WizardMoves:
        """fire_stones = state.get_all_tile_locations(FireStone)
        ice_stones = state.get_all_tile_locations(IceStone)
        grid_size = state.grid_size
        wizard_location = state.active_entity_location
        # TODO: YOUR CODE HERE"""
        if self.moves:
            return self.moves.pop(0)
        return WizardMoves.STAY # No moves left, just stay in place (shouldn't happen if the puzzle is solvable)




class SpellCastingPuzzleWizard(WizardAgent):
    def __init__(self, initial_state: GameState):
        self.actions: list[GameAction] = self._solve(initial_state)
    def _try_assignment(self, state: GameState, assignment: dict):
        #Apply the given assignment of moves/spells to the state and check if it solves the puzzle (all stones covered and valid path)
        # Returns movelist if it solves the puzzle, otherwise None
        new_state = state
        for location, is_fire in assignment.items():
            new_tile = FireStone() if is_fire else IceStone()
            new_state = new_state.replace_tile(location.row, location.col, new_tile)
        fire_locations = new_state.get_all_tile_locations(FireStone)
        ice_locations = new_state.get_all_tile_locations(IceStone)
        solver, hedge, vedge, R, C, wizard_location = build_maysu_solver(new_state, fire_locations, ice_locations)
        if solver.check() == z3.sat:
            return extract_path(solver.model(), wizard_location, hedge, vedge, R, C)
        return None
    
    def _build_actions(self, path_moves: list, assignment: dict, wizard_location: Location):
        #Build a list of GameActions (moves and NOW spells) to execute the path_moves while ensuring the stones in the assignment are covered correctly
        actions: list[GameAction] = []

        #Edge case: wizard starts on a stone, need to cast spell on the first turn before moving
        if wizard_location in assignment:
            spell = WizardSpells.FIREBALL if assignment[wizard_location] else WizardSpells.FREEZE
            actions.append(spell)
        current_location = wizard_location
        for move in path_moves:
            actions.append(move)
            dr, dc = move.value
            next_location = Location(current_location.row + dr, current_location.col + dc)
            #Insert spell if we just moved onto a stone that needs to be covered (not when closing loop back to starting location)
            if next_location in assignment and next_location != wizard_location:
                spell = WizardSpells.FIREBALL if assignment[next_location] else WizardSpells.FREEZE
                actions.append(spell)
            current_location = next_location
        return actions  
    
    def _solve(self, state: GameState):
        neutral_locations = state.get_all_tile_locations(NeutralStone)
        N = len(neutral_locations)
        wizard_location = state.active_entity_location

        if N == 0:
            # No neutral stones, just solve like a normal Maysu puzzle
            return PuzzleWizard(state).moves

        #Generate all assignments by ascending mana cost (so first solvable is cheapest) (False (ice). = 10 mana, True (fire) = 15 mana)
        all_assignments = sorted(self.generate_assignments(neutral_locations), key=lambda a: sum(15 if v else 10 for v in a.values()))

        for assignment in all_assignments:
            path_moves = self._try_assignment(state, assignment)
            if path_moves is not None:
                return self._build_actions(path_moves, assignment, wizard_location)
        
        print("SpellCastingPuzzleWizard: No solution found for the given puzzle")
        return []

    def generate_assignments(locations: list):
        #Generates all possible assignments of True/False for the given locations, sorted by ascending mana cost (False (ice). = 10 mana, True (fire) = 15 mana)
        assignments = [{}]
        for loc in locations:
            new_assignments = []
            for existing in assignments:
                fire_version = {**existing, loc: True} # Assign fire to this location
                ice_version = {**existing, loc: False} # Assign ice to this location
                new_assignments.append(fire_version)
                new_assignments.append(ice_version)
            assignments = new_assignments
        return assignments



    
    
    def react(self, state: GameState) -> GameAction:
        """fire_stones = state.get_all_tile_locations(FireStone)
        ice_stones = state.get_all_tile_locations(IceStone)
        neutral_stones = state.get_all_tile_locations(NeutralStone)

        grid_size = state.grid_size
        wizard_location = state.active_entity_location

        # TODO: YOUR CODE HERE"""
        if self.actions:
            return self.actions.pop(0)
        return WizardMoves.STAY # No actions left, just stay in place (shouldn't happen if the puzzle is solvable)






"""
Here are some reference solutions for some of the included puzzle maps you can use to help you test things
"""

MASYU_1_SOLUTION =[WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP]


MASYU_2_SOLUTION =[WizardMoves.RIGHT,WizardSpells.FIREBALL,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardSpells.FREEZE,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardSpells.FIREBALL,WizardMoves.RIGHT]
