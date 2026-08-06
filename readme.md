# Frama-C ARMv8

Automatically generate HOL4 ARMv8 contracts from ACSL contract annotations.

### Requirements

1. Linux/WSL
2. OCaml and dune installed 
3. Frama-C installed from https://git.frama-c.com/pub/frama-c
4. HOLBA installed from https://github.com/kth-step/HolBA/tree/master

### Building

1. `cd ~`
2. `git clone https://git.frama-c.com/pub/frama-c`
3. `cd ~/frama-c/src/plugins/`
4. `git clone https://github.com/VincentLagerros/frama-c-arm8`
5. `cd frama-c-arm8`
6. Run with `dune build && dune exec -- frama-c -arm8 "[C file]" -arm8-type="hol"` or alternatively `./run.sh` 

### Testing

Generated hol files can test build by editing the `spec_arm8Script.sml` template.

1. `source ~/HolBA/env.sh`
2. `cd ~/frama-c/src/plugins/frama-c-arm8/hol-template`
3. `Holmake` 

### Flags

`-arm8` Enables the plugin

`-arm8-output <file>` Specify the output destination

`-arm8-type <hol|py|dbg>` Specify the output format, default is Hol4 (`hol`)

`-arm8-acsl` Enables pretty printing of the ensures/requires clause as a HOL comment