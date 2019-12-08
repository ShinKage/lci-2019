# Final Project for LCE 2019-2020

A visibile LLVM toolchain is required.

To build the project: `stack build`
 
To execute the compiled project: `stack exec lab-exe`

### CLI
At this time, the executable parses a single valid expression and prints the untyped AST followed by the typechecked AST, with the resulting expression type. Five command are supported:
- `eval`: the expression will be interpreted and the result printed to the stdout
- `jit`: execute the expression inside the CLI using a LLVM JIT (only a subset of the language is supported)
- `llvm`: prints the generated LLVM IR (only a subset of the language is supported)
- `compile`: prints the generated ASM from the LLVM IR compilation (only a subset of the language is supported)
- `pretty`: prints a pretty-printed version of the typed AST (the syntax is not the same of the parsed language, only for debug purpose, not formatting)

## TODO (?)
- [ ] Using a custom monad for error reporting both in codegen and parsing phase.
- [ ] Add some syntactic sugar to the language syntax
- [ ] Finish the typechecker and evaluator formal specification
- [ ] Codegen for closures
- [ ] Optimization on the typechecked AST (constant expression evaluation, constant folding, dead-code elimination, ...)
- [ ] Add support for ADTs (newtype or isomorphism?)
- [ ] Fully functional REPL
