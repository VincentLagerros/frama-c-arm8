import z3
from z3 import *

def check_overflow(name : str, input_contract):
    local_solver = Solver()
    result = local_solver.check(Not(input_contract))
    if result == unsat:
        print(f"Contract {name} is correct")
    elif result == unknown:
        print(f"Contract {name} is unknown")
    else:
        print(f"Contract {name} is invalid for model = {local_solver.model()}")

print("====== Checking if a contract will result in wrong behavior with overflow ======")

# Auto generated

# Function max
_result = BitVec("\\result", 64)
x = BitVec("x", 64)
y = BitVec("y", 64)
check_overflow("max", (And(True, And(And(Or(_result==x, _result==y), _result>=x), _result>=y)) == And(True, And(And(Or(_result==x, _result==y), _result>=x), _result>=y))))

# Function inc
_result = BitVec("\\result", 64)
x = BitVec("x", 64)
check_overflow("inc", (And(x<9223372036854775807, If(BVAddNoOverflow(x, 1, True), _result==x + 1, FreshBool())) == And(x<9223372036854775807, If(BVAddNoOverflow(x, 1, True), _result==x + 1, FreshBool()))))

# Function incorrect_inc
_result = BitVec("\\result", 64)
x = BitVec("x", 64)
check_overflow("incorrect_inc", (And(True, If(BVAddNoOverflow(x, 1, True), _result==x + 1, FreshBool())) == And(True, If(BVAddNoOverflow(x, 1, True), _result==x + 1, FreshBool()))))

# Function test_invalid
_result = BitVec("\\result", 64)
x = BitVec("x", 64)
check_overflow("test_invalid", (And(True, If(BVAddNoOverflow(x, 1, True), x + 1<=9223372036854775807, FreshBool())) == And(True, If(BVAddNoOverflow(x, 1, True), x + 1<=9223372036854775807, FreshBool()))))

# Function main
_result = BitVec("\\result", 64)
check_overflow("main", (And(True, True) == And(True, True)))