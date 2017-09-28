# FDV - FD verifier

This script automatically applies the solution to a constraint problem to the input string for that problem and tells you whether the solution is correct.

It is used to verify the results in test cases for [fdo](https://github.com/qfox/fdo) and [fdp](https://github.com/qfox/fdp), which are finite domain constraint problem solvers.

The limitation lies in that it only supports one constraint per line. That means that nested or grouped constraints cannot be verified by this verifier. It's really just a tool for testing so we control these problems. This way we don't have to write an actual parser but can do simple regular expression manipulations on the input problem to determine the constraints used.

See [fdq](https://github.com/qfox/fdq) for details on this project and [fdh](https://github.com/qfox/fdh) for many examples where this verifier is used.
