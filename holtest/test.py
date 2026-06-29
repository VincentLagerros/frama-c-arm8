#!/usr/bin/env python3

# Sanity check for code generation, to check that it can be parsed by hol
# Right now `1w = 1w` does not as it is not typed, for all practical purposes this is a non-issue

# Note that `dune build` need to be ran in the root

from os import system
import os
import time
folder = "acsl-by-example/"
dir_list = sorted(os.listdir(folder))

for file in dir_list:
    if not file.endswith(".c"):
        continue
    start = time.time()
    print(f"============ Testing {file} ============")
    
    #if (input().strip()) != "":
    #    break

    hol_result = -1
    compile_result = -1
    hol_time = start
    compile_result = system(f'cat ../hol-template/spec_arm8Script.sml > spec_arm8Script.sml && dune exec -- frama-c -arm8 {folder}{file} -arm8-type="hol" -verbose 0 -debug 0 >> spec_arm8Script.sml')
    compile_time = time.time()

    if compile_result:
        system(f"cp spec_arm8Script.sml compile-error/{file.replace(".c", ".sml")}")
    else:
        system(f"cp spec_arm8Script.sml compile-success/{file.replace(".c", ".sml")}")
        hol_result = system('Holmake')
        hol_time = time.time()
        if hol_result:
            system(f"cp spec_arm8Script.sml hol-error/{file.replace(".c", ".sml")}")
    
    system(f"echo \"{compile_time-start} {hol_time-start} {compile_result} {hol_result}\" > stats/{file.replace(".c", ".txt")}")