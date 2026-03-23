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

# Old Variables
old_1 = BitVec('old_1', 64)
old_0 = BitVec('old_0', 64)

# Pre State
REG = Array('REG(s)', BitVecSort(64), BitVecSort(64))
MEM = Array('MEM(s)', BitVecSort(64), BitVecSort(64))

# Pre Contract
OldVar = And(old_1 == REG[0], old_0 == REG[1])
Requires = True

# Post State
REG = Array('REG(s\')', BitVecSort(64), BitVecSort(64))
MEM = Array('MEM(s\')', BitVecSort(64), BitVecSort(64))

# Post Contract
Ensures = And(And(Or(REG[0] == old_1, REG[0] == old_0), REG[0] >= old_1), REG[0] >= old_0)

# Bindings
P = And(OldVar, Requires)
R = Ensures

# Manually written
Q = REG[0] == If(old_1 > old_0, old_1, old_0)
try_contract("max", P, Q, R)
