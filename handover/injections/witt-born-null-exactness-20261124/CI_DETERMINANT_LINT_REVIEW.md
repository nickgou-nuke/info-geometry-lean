# Independent review: determinant simplifier cleanup

Reviewed the integrated diff in
`lean/InfoGeometry/Algebra/ZornLeftDeterminant.lean` against the extracted
GitHub run `45410082037` receipts and module log.

Reviewed source SHA-256:
`25aaf00c189af0cf97d087c49a651903b3355b54102be89f2a2161edc559aa7a`.

The complete source diff removes exactly the three arguments named by the
native compiler's fatal `unusedSimpArgs` diagnostics:

| Original line | Removed argument | Resulting tactic |
| --- | --- | --- |
| 121 | `Equiv.Perm.sign_swap` | `simp [s0, s1, s2, s3]` |
| 147 | `Matrix.det_smul` | `simp [hCB]` |
| 162 | `zero_add` | `simp only [mul_one, one_mul, zero_mul, mul_zero, add_zero]` |

Each resulting tactic is exactly the compiler's suggested replacement.
No theorem statement, surrounding proof structure, simplifier linter option,
warning-as-error setting, dependency pin, or acceptance gate is changed.

The observed run establishes that the corrected dependency bootstrap reached
actual repository elaboration. The separate supplied-counterexample suite
completed compilation and audited 17 owned declarations, permitting only
`propext`, `Classical.choice`, and `Quot.sound`. Its audit passed.

The full selected suite stopped at this determinant owner with exactly the
three linter diagnostics above. Its complete axiom audit did not run. Those
observations do not certify the later hierarchy or Witt/Born owners.

Disposition: approve this surgical source correction for the next native
run. This reviewer ran no local compiler, build, test, or axiom audit.
