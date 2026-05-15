# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:11.376580+00:00`
Root: `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **20**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean` | `advisory` | 44 | 0 | 20 | 4 | 24 |

## Findings by file

### `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean`
- module: `InfoGeometry.Canonical.GrandCanonicalExperts`
- status: `advisory`
- debt_score: `44`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `simp-law-injection` in `simp-declaration cliffordBasis_plus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L31 [soft] `simp-law-injection` in `simp-declaration cliffordBasis_minus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L32 [soft] `simp-law-injection` in `simp-declaration splitQ11_splitBasisPlus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L36 [soft] `simp-law-injection` in `simp-declaration splitQ11_splitBasisMinus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L40 [soft] `simp-law-injection` in `simp-declaration splitB11_splitBasis_orthogonal` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L150 [soft] `simp-law-injection` in `simp-declaration parity_plus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L152 [soft] `simp-law-injection` in `simp-declaration parity_minus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L158 [soft] `simp-law-injection` in `simp-declaration superSign_plus_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L162 [soft] `simp-law-injection` in `simp-declaration superSign_plus_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L166 [soft] `simp-law-injection` in `simp-declaration superSign_minus_minus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L178 [soft] `simp-law-injection` in `simp-declaration splitSuperBracket_plus_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L184 [soft] `simp-law-injection` in `simp-declaration splitSuperBracket_plus_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L190 [soft] `simp-law-injection` in `simp-declaration splitSuperBracket_minus_minus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L199 [soft] `law-field-locker` in `structure-field SplitCliffordSuperData.label` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `skeletal-proof` in `lemma labelGenerator_sq` — proof appears to close via minimal tactic one-liner
  - L224 [soft] `simp-law-injection` in `simp-declaration labelGenerator_sq_plus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L230 [soft] `simp-law-injection` in `simp-declaration labelGenerator_sq_minus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L340 [soft] `simp-law-injection` in `simp-declaration diracAction_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L347 [soft] `simp-law-injection` in `simp-declaration diracEulerStep_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L351 [soft] `skeletal-proof` in `lemma diracAction_add_right` — proof appears to close via minimal tactic one-liner
  - L371 [advisory] `existential-packaging` in `def parityEntropy` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L383 [advisory] `existential-packaging` in `theorem exists_clifford_labeled_state_of_bistochastic` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L407 [advisory] `existential-packaging` in `theorem exists_modewiseClifford_rep_of_bistochastic` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

