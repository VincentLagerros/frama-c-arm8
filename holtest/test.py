#!/usr/bin/env python3

# Sanity check for code generation, to check that it can be parsed by hol
# Right now `1w = 1w` does not as it is not typed, for all practical purposes this is a non-issue

# Note that `dune build` need to be ran in the root

from os import system

def check(result):
    if result:
        print(f"Error {result}")
        exit(result)

for i in range(6):
    result = system(f'cat ../hol-template/spec_arm8Script.sml > spec_arm8Script.sml && dune exec -- frama-c -arm8 tests/{i}.c -arm8-type="hol" -verbose 0 -debug 0 >> spec_arm8Script.sml')
    check(result)
    result = system('Holmake')
    check(result)