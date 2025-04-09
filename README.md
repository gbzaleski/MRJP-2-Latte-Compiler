# Latte compiler
Haskell compiler for the imperative language Latte. \
Course at the University of Warsaw.

## Task description
https://www.mimuw.edu.pl/~ben/Zajecia/Mrj2023/Latte/ \
https://www.mimuw.edu.pl/~ben/Zajecia/Mrj2023/latte.html

## Running project
```
make
```
then
```
./latc_llvm input_file.lat
```

## Project content
 * Frontend typechecker
 * Base Latte compiler
 * Usage of `alloca` and `store` for variable allocation and value updating instead of `phi` function approach
 * Pooling string values
 * Constant & literals usage and propagation for code optimisation
 * Unreachable code cleanup
 * Subexpression evaluation
 * Dead code elimination
 * Structures
 * Class extension/inheritance
 * Class methods
 * Virtual class methods
 * Calloc usage for starting values

 ## Requirements
 * Haskell
 * C
 * LLVM
 * Clang compiler
 * Makefile

## Repo structure
 * `.hs` - Haskell source files
 * `Latte.cf` - Language grammar
 * `Makefile` - Makefile file for compilation
 * `lattest/` - Tests for compiler
 * `Latte/` - Haskell parser files
 * `test.sh` - Bash file for running tests (requires compiled latc_llvm executable file beforehand)
 * `lib/runtime.c` - Standard library functions implemented in C language (then added to the project during compilation)

 ## Result files 
 * `.ll` - LLVM source code
 * `.bc` - bitcode file (to be run with `lli`)
