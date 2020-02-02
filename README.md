# Final Project for LCI 2019-2020

A visibile LLVM toolchain is required.

To build the project: `stack build`
 
To execute the compiled project: `stack exec lab-exe`

To execute tests: `stack test`

### CLI
At this time, the executable parses a single valid expression that can be interpreted or compiled to the LLVM IR for JIT compilation or ASM compilation. The supported commands are:
- `eval`: the expression will be interpreted and the result printed to the stdout
- `step`: each step of the expression interpretation will be printed
- `jit`: execute the expression inside the CLI using a LLVM JIT (only a subset of the language is supported)
- `llvm`: prints the generated LLVM IR (only a subset of the language is supported)
- `compile`: prints the generated ASM from the LLVM IR compilation (only a subset of the language is supported)
- `pretty`: prints a pretty-printed version of the typed AST (the syntax is not the same of the parsed language, only for debug purpose, not formatting)
- `typed`: prints the typed AST
- `untyped`: prints the untyped AST obtained from parsing
- `codegen`: prints the IR produced for the LLVM IR code generation
- `expr`: evaluates another expression
- `quit`: exits the CLI
