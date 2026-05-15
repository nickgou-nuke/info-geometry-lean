# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:33.525639+00:00`
Root: `lean/InfoGeometry/Canonical/NoncommutativeModularSignum.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **34**
- Hard: **0**
- Soft: **21**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/NoncommutativeModularSignum.lean` | `advisory` | 55 | 0 | 21 | 13 | 34 |

## Findings by file

### `lean/InfoGeometry/Canonical/NoncommutativeModularSignum.lean`
- module: `InfoGeometry.Canonical.NoncommutativeModularSignum`
- status: `advisory`
- debt_score: `55`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L70 [soft] `simp-law-injection` in `simp-declaration leftMul_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `skeletal-proof` in `theorem leftMul_apply` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `simp-law-injection` in `simp-declaration rightMul_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `skeletal-proof` in `theorem rightMul_apply` — proof appears to close via minimal tactic one-liner
  - L111 [soft] `simp-law-injection` in `simp-declaration lrRelativeModular_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L114 [soft] `skeletal-proof` in `theorem lrRelativeModular_apply` — proof appears to close via minimal tactic one-liner
  - L168 [soft] `simp-law-injection` in `simp-declaration boostSignum_of_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L170 [soft] `skeletal-proof` in `theorem boostSignum_of_pos` — proof appears to close via minimal tactic one-liner
  - L173 [soft] `simp-law-injection` in `simp-declaration boostSignum_of_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L177 [advisory] `local-hypothesis-injection` in `theorem boostSignum_of_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L179 [soft] `simp-law-injection` in `simp-declaration boostSignum_of_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L181 [soft] `skeletal-proof` in `theorem boostSignum_of_zero` — proof appears to close via minimal tactic one-liner
  - L194 [advisory] `local-hypothesis-injection` in `theorem boostSignum_sq_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L202 [soft] `skeletal-proof` in `theorem conjugate_involution_axis` — proof appears to close via minimal tactic one-liner
  - L207 [advisory] `local-hypothesis-injection` in `theorem conjugate_involution_axis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L217 [soft] `skeletal-proof` in `theorem conjugate_boostHamiltonian` — proof appears to close via minimal tactic one-liner
  - L223 [advisory] `local-hypothesis-injection` in `theorem conjugate_boostHamiltonian` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L225 [advisory] `local-hypothesis-injection` in `theorem conjugate_boostHamiltonian` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L243 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L245 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L246 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L247 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L267 [soft] `simp-law-injection` in `simp-declaration doubledBoostSignum_of_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L269 [soft] `skeletal-proof` in `theorem doubledBoostSignum_of_pos` — proof appears to close via minimal tactic one-liner
  - L272 [soft] `simp-law-injection` in `simp-declaration doubledBoostSignum_of_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L277 [soft] `simp-law-injection` in `simp-declaration doubledBoostSignum_of_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L279 [soft] `skeletal-proof` in `theorem doubledBoostSignum_of_zero` — proof appears to close via minimal tactic one-liner
  - L295 [soft] `skeletal-proof` in `theorem modular_j_conjugates_doubledBoostHamiltonian` — proof appears to close via minimal tactic one-liner
  - L298 [advisory] `local-hypothesis-injection` in `theorem modular_j_conjugates_doubledBoostHamiltonian` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L302 [advisory] `local-hypothesis-injection` in `theorem modular_j_conjugates_doubledBoostHamiltonian` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L308 [soft] `skeletal-proof` in `theorem modular_j_conjugates_doubledBoostDelta` — proof appears to close via minimal tactic one-liner
  - L320 [soft] `skeletal-proof` in `theorem doubledBoostSignum_cl11_relations_of_pos` — proof appears to close via minimal tactic one-liner
  - L325 [advisory] `local-hypothesis-injection` in `theorem doubledBoostSignum_cl11_relations_of_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

