Instructional (and WIP) lazy purely-functional programming language with pattern
matching, based on graph reduction.

It is meant as an extended exercise in the design and implementation of lazy
functional programming languages in Haskell, while reading 'The Implementation
of Functional Programming Languages' by Simon Peyton Jones.

While a good deal of functionality is already implemented, we can't run programs
yet as several parts of the compiler need glue code (which is not there yet)
connecting them together.

Some implemented and missing features are:

- [x] Lexing/parsing via Alex/Happy
- [x] Desugaring of source syntax to Core
  - [x] Data declarations
  - [x] Patterns
  - [x] Type inference
- [ ] Core-to-Core transformations
  - [x] Dependency analysis
  - [ ] Case stripping (most of it)
  - [x] Lambda lifting
- [ ] GMachine execution
  - [ ] Compiling case-stripped, lambda-lifted Core to GMachine bytecode (most of it)
  - [x] Executing GMachine byte code

### Build and run

Build with `cabal build`. Run with `cabal run`. As of now, the program accepts
source files passed as argument and dumps a (somewhat pretty-printed)
desugared Core with inferred types.
For example, running `cabal run fp-lang -- example_program` results in

``` sh
fib : (Int) -> Int
fib = \ x0 -> case ((eql#) (x0)) (0) of
          True -> 0
          False -> case ((eql#) (x0)) (1) of
                     True -> 1
                     False -> ((add#) ((fib) (((sub#) (x0)) (1)))) ((fib) (((sub#) (x0)) (2)))
main : Int
main = (fib) (3)
```
