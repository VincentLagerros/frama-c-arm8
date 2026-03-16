import z3
from z3 import *


def try_contract(name: str, P, Q, R):
    local_solver = Solver()
    result = local_solver.check(And(P, Q))
    if result == unsat:
        print(f"Contract {name} is invalid, no path-condition exists")
    elif result == unknown:
        print(f"Contract {name} is unknown")
    else:
        result = local_solver.check(And(P, Q, Not(R)))
        if result == unsat:
            print(f"Contract {name} is correct")
        elif result == unknown:
            print(f"Contract {name} is unknown")
        else:
            print(f"Contract {name} is invalid for model = {local_solver.model()}")


print("====== Checking the contract with Z3 ======")

# ================= Auto generated =================

# ==== Function max ====

# Pre Variables
x = Int('x')
y = Int('y')

# Old Variables
old_3 = Int('old_3')
old_2 = Int('old_2')
old_1 = Int('old_1')
old_0 = Int('old_0')

# Pre State
REG = Array('REG(s)', IntSort(), IntSort())
MEM = Array('MEM(s)', IntSort(), IntSort())

# Pre Contract
PreVar = And(x == REG[0], y == REG[1])
OldVar = And(And(And(old_3 == y, old_2 == x), old_1 == x), old_0 == y)
Requires = True

# Post State
REG = Array('REG(s\')', IntSort(), IntSort())
MEM = Array('MEM(s\')', IntSort(), IntSort())

# Post Contract
Ensures = And(And(Or(REG[0] == old_1, REG[0] == old_0), REG[0] >= old_2), REG[0] >= old_3)

# Bindings
P = And(PreVar, OldVar, Requires)
R = Ensures

# Manually written
Q = REG[0] == If(x > y, x, y)
try_contract("max", P, Q, R)
