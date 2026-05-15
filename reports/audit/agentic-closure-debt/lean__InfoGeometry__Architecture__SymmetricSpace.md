# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:31.629971+00:00`
Root: `lean/InfoGeometry/Architecture/SymmetricSpace.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **12**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Architecture/SymmetricSpace.lean` | `advisory` | 28 | 0 | 12 | 4 | 16 |

## Findings by file

### `lean/InfoGeometry/Architecture/SymmetricSpace.lean`
- module: `InfoGeometry.Architecture.SymmetricSpace`
- status: `advisory`
- debt_score: `28`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L13 [soft] `law-field-locker` in `structure-field SymmetricSpace.symmetry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L15 [soft] `law-field-locker` in `structure-field SymmetricSpace.symm_involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L17 [soft] `law-field-locker` in `structure-field SymmetricSpace.symm_fixpoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L19 [soft] `simp-law-injection` in `simp-declaration symmetry_symmetry` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L26 [soft] `simp-law-injection` in `simp-declaration symmetry_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `law-field-locker` in `structure-field CartanInvolution.involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field SymmetricPair.fix_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [advisory] `local-hypothesis-injection` in `def fixedSubgroup` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L75 [advisory] `local-hypothesis-injection` in `def fixedSubgroup` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L79 [advisory] `local-hypothesis-injection` in `def fixedSubgroup` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L83 [soft] `simp-law-injection` in `simp-declaration mem_fixedSubgroup_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration CartanInvolution.mem_fixedSubgroup_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `skeletal-proof` in `lemma cartanSymmetry_involutive` — proof appears to close via minimal tactic one-liner
  - L153 [soft] `skeletal-proof` in `lemma cartanSymmetryOfInvolutiveMulAut_involutive` — proof appears to close via minimal tactic one-liner
  - L161 [soft] `skeletal-proof` in `lemma cartanSymmetryOfInvolutiveMulAut_fixpoint` — proof appears to close via minimal tactic one-liner

