# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:53.594344+00:00`
Root: `lean/InfoGeometry/Canonical/Cl11LorentzAction.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **14**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/Cl11LorentzAction.lean` | `advisory` | 40 | 0 | 14 | 12 | 26 |

## Findings by file

### `lean/InfoGeometry/Canonical/Cl11LorentzAction.lean`
- module: `InfoGeometry.Canonical.Cl11LorentzAction`
- status: `advisory`
- debt_score: `40`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L29 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L60 [soft] `skeletal-proof` in `theorem cartan_commutator_uPlus` — proof appears to close via minimal tactic one-liner
  - L74 [soft] `skeletal-proof` in `theorem cartan_commutator_uMinus` — proof appears to close via minimal tactic one-liner
  - L112 [soft] `skeletal-proof` in `theorem cartan_flow_scales_uPlus_exp` — proof appears to close via minimal tactic one-liner
  - L119 [soft] `skeletal-proof` in `theorem cartan_flow_scales_uMinus_exp` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `skeletal-proof` in `theorem modular_flow_scales_uPlus` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `skeletal-proof` in `theorem modular_flow_scales_uMinus` — proof appears to close via minimal tactic one-liner
  - L166 [soft] `skeletal-proof` in `theorem modularFlow_mul_modularFlow_neg` — proof appears to close via minimal tactic one-liner
  - L173 [advisory] `local-hypothesis-injection` in `theorem modularFlow_mul_modularFlow_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L175 [advisory] `local-hypothesis-injection` in `theorem modularFlow_mul_modularFlow_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L191 [soft] `skeletal-proof` in `theorem modularFlow_neg_mul_modularFlow` — proof appears to close via minimal tactic one-liner
  - L198 [advisory] `local-hypothesis-injection` in `theorem modularFlow_neg_mul_modularFlow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L200 [advisory] `local-hypothesis-injection` in `theorem modularFlow_neg_mul_modularFlow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L234 [advisory] `bridge-shaped-declaration` in `theorem modularFlow_lieExponential_transport_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L256 [soft] `skeletal-proof` in `theorem uPlus_mul_modularFlow_neg` — proof appears to close via minimal tactic one-liner
  - L262 [advisory] `local-hypothesis-injection` in `theorem uPlus_mul_modularFlow_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L283 [soft] `skeletal-proof` in `theorem uMinus_mul_modularFlow_neg` — proof appears to close via minimal tactic one-liner
  - L289 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_modularFlow_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L317 [soft] `skeletal-proof` in `theorem modularAdjointFlow_add` — proof appears to close via minimal tactic one-liner
  - L337 [soft] `skeletal-proof` in `theorem modularAdjointFlow_scales_uPlus` — proof appears to close via minimal tactic one-liner
  - L341 [advisory] `local-hypothesis-injection` in `theorem modularAdjointFlow_scales_uPlus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L360 [soft] `skeletal-proof` in `theorem modularAdjointFlow_scales_uMinus` — proof appears to close via minimal tactic one-liner
  - L364 [advisory] `local-hypothesis-injection` in `theorem modularAdjointFlow_scales_uMinus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L383 [soft] `skeletal-proof` in `theorem modularAdjointFlow_fixes_gZeroPart` — proof appears to close via minimal tactic one-liner

