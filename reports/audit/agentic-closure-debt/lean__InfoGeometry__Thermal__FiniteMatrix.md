# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:46.112817+00:00`
Root: `lean/InfoGeometry/Thermal/FiniteMatrix.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **41**
- Hard: **0**
- Soft: **33**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermal/FiniteMatrix.lean` | `advisory` | 74 | 0 | 33 | 8 | 41 |

## Findings by file

### `lean/InfoGeometry/Thermal/FiniteMatrix.lean`
- module: `InfoGeometry.Thermal.FiniteMatrix`
- status: `advisory`
- debt_score: `74`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [soft] `law-field-locker` in `structure-field DiagonalObservable.coeff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L29 [soft] `law-field-locker` in `structure-field DiagonalObservable.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field DiagonalObservable.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field DiagonalObservable.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field DiagonalObservable.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `law-field-locker` in `structure-field DiagonalObservable.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field DiagonalObservable.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field DiagonalObservable.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field DiagonalObservable.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `simp-law-injection` in `simp-declaration zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration one_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L42 [soft] `simp-law-injection` in `simp-declaration add_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L43 [soft] `simp-law-injection` in `simp-declaration sub_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `simp-law-injection` in `simp-declaration neg_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `simp-law-injection` in `simp-declaration mul_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L46 [soft] `simp-law-injection` in `simp-declaration smul_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [advisory] `existential-packaging` in `def toMatrix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L51 [soft] `simp-law-injection` in `simp-declaration toMatrix_apply_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `simp-law-injection` in `simp-declaration toMatrix_apply_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `law-field-locker` in `structure-field Hamiltonian.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [advisory] `existential-packaging` in `def toMatrix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L80 [soft] `simp-law-injection` in `simp-declaration toMatrix_apply_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `skeletal-proof` in `lemma partition_pos` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `skeletal-proof` in `lemma gibbsWeight_pos` — proof appears to close via minimal tactic one-liner
  - L109 [soft] `skeletal-proof` in `lemma gibbsWeight_sum_one` — proof appears to close via minimal tactic one-liner
  - L128 [advisory] `existential-packaging` in `def densityMatrix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L134 [soft] `simp-law-injection` in `simp-declaration densityMatrix_apply_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L139 [soft] `simp-law-injection` in `simp-declaration densityMatrix_apply_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L146 [soft] `simp-law-injection` in `simp-declaration diagonalMass_densityMatrix` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L155 [soft] `simp-law-injection` in `simp-declaration thermalState_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L172 [advisory] `existential-packaging` in `def internalEnergy` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L178 [soft] `skeletal-proof` in `lemma internalEnergy_eq_gibbsExpectation` — proof appears to close via minimal tactic one-liner
  - L181 [advisory] `existential-packaging` in `def modularShift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L186 [soft] `simp-law-injection` in `simp-declaration modularShift_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L190 [soft] `simp-law-injection` in `simp-declaration modularShift_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L194 [soft] `simp-law-injection` in `simp-declaration modularShift_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L198 [soft] `simp-law-injection` in `simp-declaration modularShift_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L203 [soft] `skeletal-proof` in `lemma thermalState_modularShift_invariant` — proof appears to close via minimal tactic one-liner
  - L207 [advisory] `existential-packaging` in `def SatisfiesDiagonalKMS` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L215 [advisory] `existential-packaging` in `theorem satisfiesDiagonalKMS` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

