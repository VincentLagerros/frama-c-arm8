import z3
from z3 import *

def try_contract(name: str, P, Q, R):
    local_solver = Solver()
    result = local_solver.check(And(P, Q, Not(R)))
    if result == unsat:
        print(f"Contract {name} is correct")
    elif result == unknown:
        print(f"Contract {name} is unknown")
    else:
        print(f"Contract {name} is invalid for model = {local_solver.model()}")


print("====== Checking the contract with Z3 ======")

# Auto generated

# Function max
_result = Int("\\result")
x = Int("x")
y = Int("y")
P = True
R = And(And(Or(_result == x, _result == y), _result >= x), _result >= y)

# Manually written
Q = _result == If(x > y, x, y)
try_contract("max", P, Q, R)
