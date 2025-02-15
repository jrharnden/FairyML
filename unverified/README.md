Various unverified tools, e.g. tools for converting OCaml to CakeML
and an SML version of the CakeML register allocator.

[ocaml-syntax](ocaml-syntax):
An OCaml to CakeML translator. Attempts to translate type-correct OCaml files
to equivalent CakeML files. Multi-file programs should be supported eventually,
but are not currently.

[reg_alloc](reg_alloc):
A snapshot of the register allocator from the CakeML compiler, translated from
HOL to CakeML then pretty-printed in Standard ML syntax.

[sexpr-bootstrap](sexpr-bootstrap):
An alternative bootstrapping process: The translated AST of the compiler is
printed as an S-expression then fed into a previously built executable of the
CakeML compiler.
