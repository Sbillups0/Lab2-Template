import z3
from z3 import (Solver, Bool,Bools,Int,Ints, Or, Not, And, Implies, Xor, BitVec, BV2Int, Reals, Distinct, If)

"""
Suppose we want to find a satisfying assignment for the expression (a || !b) && (!a || c). That means we're looking for values of a, b, and c that make the entire expression evaluate to true.

One way to approach this is by checking all possible combinations of truth values for a, b, and c. Since each variable can be either true or false, there are 2^3=8 possible combinations.

Can you list all 8 combinations of a, b, and c?

In general, for n variables, there will be 2^n possible assignments, so the approach of "trying everything" is not efficient for large n. In fact, this is the SAT ("satisfiability") problem, which is NP-complete, meaning that it is "one of the hardest problems to which solutions can be verified quickly. But this difficult problem is exactly what tools like the Z3 SMT solver! Here’s how we can solve the problem using the Z3:
"""
def boolean_expressions():
    a = Bool('a')
    b = Bool('b')
    c = Bool('c')

    s = Solver()

    clause_1 = Or(a,Not(b))
    clause_2 = Or(Not(a),c)

    s.add(clause_1)
    s.add(clause_2)

    match s.check():
        case z3.sat:
            f_1_model = s.model()
            print(f_1_model)

    """
    The output says that the formula (a || !b) && (!a || c) will be true when a, b, and c are all false.

    But what if we want a different solution?

    In this case, we can add an additional constraint that says that we don’t want the solution where a, b, and c are all false.
    """


    clause_3 = Not(And(Not(a),Not(b),Not(c)))
    s.add(clause_3)

    match s.check():
        case z3.sat:
            f_2_model = s.model()
            print(f_2_model)

    """
    This output says that the formula (a || !b) && (!a || c) will be true when b is false and c is true (it doesn’t matter what a is).

    Let’s try adding one more constraint
    """

    clause_4 = (And(Not(a),b))
    s.add(clause_4)
    match s.check():
        case z3.unsat:
            print("Unsatisfiable")
    """
    The output unsat means unsatisfiable. The solver is telling us that there is no possible choice of a, b, c that makes the current constraints true.
    """





"""
Z3 can find solutions to more than just SAT problems – it is an SMT solver.

SMT stands for SAT modulo theories; it generalizes SAT to formulas involving integers, strings, arrays, and so on (the details of how it can do this are interesting but complicated, and we probably wont be able to get to them in class). For example, we can use Z3 to find a solution for the system of equations 3x - 2y = 1, y - x = 1.
"""
def integer_expressions():
    x,y = Ints('x y')
    s=Solver()
    s.add(3*x-2*y==1)
    s.add(y-x==1)

    match s.check():
        case z3.sat:
            model = s.model()
            print(model)

"""
In addition to integers Z3 can solve systems of equations that use real numbers. These can get quite complex and also very useful potentially for some of your final projects.
"""

def real_artithmetic():
    x, y = Reals('x y')
    s=Solver()
    s.add(x != 0)
    s.add(y != 0)
    s.add(x + y == 4 * x * y)
    match s.check():
        case z3.sat:
            print (f"Model: {s.model()}")

        case z3.unsat:
            print ("UNSAT")

"""
One of the most prominent uses of SMT in industry (especially now when so much software is being produced with little else to ensure correctness) is in software verification. You can see how we can prove interesting properties about programs including relating logical properties with underlying representation properties.
"""
def integer_overflow():
    # Note this takes a long time to process!
    x = BitVec('x', 16)
    y = BitVec('y', 16)

    s=Solver()
    s.add((BV2Int(x) + BV2Int(y)) != BV2Int(x+y))
    match s.check():
        case z3.sat:
            print (f"Model: {s.model()}")

        case z3.unsat:
            print ("UNSAT")




"""
Often, SMT solvers are not used to find a solution, but to prove that no solution exists. For instance, say that we want to prove the mathematical fact y > 0 ==> x + y > x. How might we do this using z3?
"""
def proof_by_unsat():
    # y>0 => x+y > x
    x,y = Ints('x y')
    s = Solver()

    # TODO: YOUR CODE HERE
    s.add(y>0)
    s.add(x+y <= x) # Negation of the statement we want to prove

    match s.check():
        case z3.unsat:
           print("The formula is UNSAT, meaning no contradiction can be found. Therefore the original formula must always be true.  QED.")


"""
Similarly, how might we try to generally prove any valid logical formula such as De Morgan's Laws?
"""
def demorgans_proof():
    p, q = Bools('p q')
    demorgan = And(p, q) == Not(Or(Not(p), Not(q)))

    def prove(f):
        """
        Print "No counterexample can be found, therefore the statement is true" if the given formula f is true, otherwise print "The formula f is false, with counterexample given by: " and the model that shows the formula to be false.
        """
        # TODO: YOUR CODE HERE
        s = Solver()
        s.add(Not(f)) # Negation of the statement we want to prove
        
        match s.check():
            case z3.unsat:
                print("No counterexample can be found, therefore the statement is true")
            case z3.sat:
                print(f"The formula f is false, with counterexample given by: {s.model()}")
        pass

    prove(demorgan)


"""
Let us try to use z3 to solve a classic kind of puzzle. You will need to come up with an encoding of the relevant part of the puzzle into variables and constraints as well translate the output of the solver into a solution.
"""
def wedding_planning():
    """
    You need to assign seating for a table of three potentially contentious wedding guests.

    There are three seats: left, middle, right.
    There are three guests: Alice, Bob, Charlie.

    The requirements are that:

    - Alice does not sit next to Charlie

    - Alice does not sit on the leftmost chair

    - Bob does not sit to the right of Charlie


    Can you find a seating arrangement that satisfies all of the guests?

    Print out either:
        The satisfying arrangement in the form "Alice sits on the left, Charlie in the middle, and Bob on the right."
    or
        "There is no acceptable seating arraignment"
    """
    #TODO: YOUR CODE HERE
    
    s = Solver()
    # Define variables for each guest's seat
    Alice = Int('Alice')
    Bob = Int('Bob')
    Charlie = Int('Charlie')
    # Each guest must sit in a different seat (1, 2, or 3)
    for guest in [Alice, Bob, Charlie]:
        s.add(And(guest >= 1, guest <= 3))
    s.add(Distinct(Alice, Bob, Charlie)) # All guests must sit in different seats
    # Alice does not sit next to Charlie
    s.add(Alice - Charlie != 1) # Alice cannot be immediately to the left of Charlie
    s.add(Charlie - Alice != 1) # Alice cannot be immediately to the right of Charlie

    s.add(Alice != 1) # Alice does not sit on the leftmost chair

    s.add(Bob < Charlie) # Bob does not sit to the right of Charlie (Bob must be in a lower numbered seat than Charlie)
    # Alice does not sit on the leftmost chair
    match s.check():
        case z3.sat:
            print(f"Acceptable seating arrangement found: {s.model()}")
        case z3.unsat:
            print("There is no acceptable seating arrangement")






"""
Lets try to solve a more complex puzzle like sudoku, given an arbitrary input.

In case you do not know, sudoku is a puzzle where the goal is to insert numbers in boxes to satisfy the following condition: each row, column, and 3x3 box must contain the digits 1 through 9 exactly once.

You will need to transform an arbitrary sudoku puzzle template (where zero represents the unfilled boxes) into a solved puzzle (or show that the puzzle is impossible).
"""

def print_sudoku(grid):
    for i,row in enumerate(grid):
        if i%3==0:
            print('-'*25)
        print(f'| {row[0]} {row[1]} {row[2]} | {row[3]} {row[4]} {row[5]} | {row[6]} {row[7]} {row[8]} |')
    print('-'*25)


def sudoku(puzzle):

    """
    Use print_sudoku to print your solution to puzzle or otherwise print "The puzzle is impossible.".
    """
    #TODO: YOUR CODE HERE
    s = Solver()
    # Create variables for each cell in the sudoku grid
    cells = [[Int(f'cell_{i}_{j}') for j in range(9)] for i in range(9)]
    # Add constraints for the given puzzle
    for i, row in enumerate(puzzle):
        for j, value in enumerate(row):
            if value != 0:
                s.add(cells[i][j] == value) # Pre-filled cells must match the given values
            else:
                s.add(And(cells[i][j] >= 1, cells[i][j] <= 9)) # Unfilled cells must be between 1 and 9 
    # Add constraints for rows, columns, and 3x3 boxes
    for i in range(9):
        s.add(Distinct(cells[i])) # Each row must contain distinct values
        s.add(Distinct([cells[j][i] for j in range(9)])) # Each column must contain distinct values
    for box_row in range(3):
        for box_col in range(3):
            s.add(Distinct([cells[i][j] for i in range(box_row*3, box_row*3+3) for j in range(box_col*3, box_col*3+3)]))  # Each 3x3 box must contain distinct values
    match s.check():
        case z3.sat:
            print(f"Solution found: {s.model()}")
        case z3.unsat:
            print("The puzzle is impossible.")



instance = ((0,0,0,0,9,4,0,3,0),
            (0,0,0,5,1,0,0,0,7),
            (0,8,9,0,0,0,0,4,0),
            (0,0,0,0,0,0,2,0,8),
            (0,6,0,2,0,1,0,5,0),
            (1,0,2,0,0,0,0,0,0),
            (0,7,0,0,0,0,5,2,0),
            (9,0,0,0,6,5,0,0,0),
            (0,4,0,9,7,0,0,0,0))



"""
The final puzzle you will solve using Z3 is the Coin Sum problem. Here in the US we have (or used to have) pennies worth 1 cent, nickels worth 5 cents, dimes worth 10 cents, quarters worth 25 cents, half dollar coins worth 50 cents, and dollar coins worth 100 cents.

It is possible to make $2 using these coins in the following way:

    1 * 1$ + 1*50c + 1*25c + 1*10c + 2*5c + 5*1c

The question is: How many ways can $2 be made using any number of coins?
"""

def coin_sum(total):
    # Variables for the numbers of each coin denomination
    # penny, nickle, dime, quarter, fifty cent coin, dollar coin
    p,n,d,q,f,c = Ints('p n d q f c')

    """
    Print the number of ways the $2 can be made using any number of the above coins.

    Hint: You may need to run many related but slightly different model checks.
    """
    # TODO: YOUR CODE HERE
    s = Solver()
    s.add(p >= 0, n >= 0, d >= 0, q>= 0, f >= 0, c >= 0) # Number of coins cannot be negative (any number of coins can be used) 
    s.add(p*1 + n*5 + d*10 + q*25 + f*50 + c*100 == total) # Total value of coins must equal the target amount

    count = 0
    while s.check() == z3.sat:
        model = s.model()
        count += 1
        # Add a constraint to exclude the current solution in the next iteration
        s.add(Or(p != model[p], n != model[n], d != model[d], q != model[q], f != model[f], c != model[c])) # Exclude
    print(f"The number of ways to make $2 is: {count}")



"""Testing outputs for the above functions"""
if __name__ == "__main__":
    print("=== boolean_expressions ===")
    boolean_expressions()

    print("\n=== integer_expressions ===")
    integer_expressions()

    print("\n=== real_arithmetic ===")
    real_artithmetic()

    print("\n=== integer_overflow ===")
    integer_overflow()  # Note: this one is slow

    print("\n=== proof_by_unsat ===")
    proof_by_unsat()

    print("\n=== demorgans_proof ===")
    demorgans_proof()

    print("\n=== wedding_planning ===")
    wedding_planning()

    print("\n=== sudoku ===")
    sudoku(instance)  # instance already defined

    print("\n=== coin_sum ===")
    coin_sum(200)  # 200 cents = $2