Translator to cv type used by cv_compute

[backend_64_cvScript.sml](backend_64_cvScript.sml):
Translate arch-size-specific functions to cv equations.

[backend_cvScript.sml](backend_cvScript.sml):
Translate non-target-specific backend functions to cv equations.

[backend_x64_cvScript.sml](backend_x64_cvScript.sml):
Translate x64-specialised functions to cv equations.

[backend_x64_evalScript.sml](backend_x64_evalScript.sml):
Experiments with evaluating the compiler using cv_compute

[eval_cake_compileLib.sml](eval_cake_compileLib.sml):
Functions for in-logic evaluation of the CakeML compiler.
These use HOL's cv_compute facility.

[eval_cake_compile_x64Lib.sml](eval_cake_compile_x64Lib.sml):
Functions for in-logic evaluation of the CakeML compiler for x64.

[to_data_cvScript.sml](to_data_cvScript.sml):
Translation of the to_data compiler function.
