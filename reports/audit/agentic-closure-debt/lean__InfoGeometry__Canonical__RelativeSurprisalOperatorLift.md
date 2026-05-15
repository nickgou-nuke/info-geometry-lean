# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:52.676742+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **41**
- Hard: **0**
- Soft: **18**
- Advisory: **23**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean` | `advisory` | 59 | 0 | 18 | 23 | 41 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`
- module: `InfoGeometry.Canonical.RelativeSurprisalOperatorLift`
- status: `advisory`
- debt_score: `59`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [advisory] `existential-packaging` in `def firstQuantize` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L48 [soft] `simp-law-injection` in `simp-declaration firstQuantize_apply_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `simp-law-injection` in `simp-declaration firstQuantize_apply_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [advisory] `existential-packaging` in `theorem firstQuantize_add` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L68 [advisory] `existential-packaging` in `theorem firstQuantize_smul` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L77 [advisory] `existential-packaging` in `theorem firstQuantize_const_eq_smul_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L102 [advisory] `existential-packaging` in `def diagonalExpectation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L109 [soft] `simp-law-injection` in `simp-declaration densityMatrixOfFinProb_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `simp-law-injection` in `simp-declaration densityMatrixOfFinProb_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration logDensityOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L127 [soft] `simp-law-injection` in `simp-declaration surprisalOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L133 [soft] `simp-law-injection` in `simp-declaration diagonalExpectation_firstQuantize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L140 [advisory] `existential-packaging` in `theorem entropy_eq_diagonalExpectation_surprisalOperator` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L176 [soft] `simp-law-injection` in `simp-declaration rayLogDensityOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L182 [soft] `simp-law-injection` in `simp-declaration relativeLogDensityOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L188 [soft] `simp-law-injection` in `simp-declaration relativeModularPotentialOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L244 [soft] `skeletal-proof` in `theorem relativeModularOperator_eq_firstQuantize_relativeDensity` — proof appears to close via minimal tactic one-liner
  - L251 [soft] `simp-law-injection` in `simp-declaration relativeLogDensityOperator_diag_eq_log_relativeModularOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L259 [soft] `simp-law-injection` in `simp-declaration relativeModularPotentialOperator_diag_eq_neg_log_relativeModularOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L285 [advisory] `existential-packaging` in `theorem relativeModularPotentialOperator_eq_firstQuantize_neg_log_relativeModularOperator_diag` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L319 [advisory] `existential-packaging` in `def modularHamiltonianReadout` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L330 [soft] `simp-law-injection` in `simp-declaration diagonalAverage_firstQuantize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L335 [soft] `simp-law-injection` in `simp-declaration modularHamiltonianReadout_eq_relativeModularHamiltonianReadout` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L353 [soft] `simp-law-injection` in `simp-declaration modularHamiltonianReadout_relativeModularOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L384 [advisory] `existential-packaging` in `theorem diagonalAverage_relativeModularPotentialOperator_eq_modularHamiltonianReadout` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L393 [advisory] `existential-packaging` in `theorem diagonalAverage_add` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L400 [advisory] `existential-packaging` in `theorem diagonalAverage_smul` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L400 [soft] `skeletal-proof` in `theorem diagonalAverage_smul` — proof appears to close via minimal tactic one-liner
  - L405 [soft] `simp-law-injection` in `simp-declaration diagonalAverage_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L412 [advisory] `local-hypothesis-injection` in `theorem diagonalAverage_smul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L416 [advisory] `local-hypothesis-injection` in `theorem diagonalAverage_smul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L420 [advisory] `existential-packaging` in `theorem relativeModularPotentialOperator_countRay_eq_raw_add_massShift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L451 [advisory] `existential-packaging` in `theorem relativeCountModularPotentialOperator_cocycle` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L520 [advisory] `local-hypothesis-injection` in `theorem relativeCountModularPotentialOperator_cocycle` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L753 [advisory] `existential-packaging` in `theorem relativeModularHamiltonian_sub_countMassShift_cocycle` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L790 [advisory] `existential-packaging` in `theorem relativeTomitaTakesakiOp_eq_modularHamiltonianReadout_relativeModularOperator_countRay_add_countMassShift_smul_id` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L822 [advisory] `existential-packaging` in `theorem relativeKreinTomitaTakesakiOp_eq_modularHamiltonianReadout_relativeModularOperator_countRay_add_countMassShift_smul_eps` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L847 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L857 [advisory] `existential-packaging` in `theorem hasDerivAt_informationPartitionFunction_zero_relativeTomitaTakesakiOp` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L869 [advisory] `existential-packaging` in `theorem hasDerivAt_logInformationPartitionFunction_zero_relativeTomitaTakesakiOp_of_normalized` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

