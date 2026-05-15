# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:03.985086+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinMPChiralHodgeConeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **8**
- Advisory: **16**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinMPChiralHodgeConeBridge.lean` | `advisory` | 32 | 0 | 8 | 16 | 24 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinMPChiralHodgeConeBridge.lean`
- module: `InfoGeometry.Canonical.DrazinMPChiralHodgeConeBridge`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L62 [soft] `skeletal-proof` in `theorem hodgeChiralityStar_sq_one` — proof appears to close via minimal tactic one-liner
  - L67 [advisory] `local-hypothesis-injection` in `theorem hodgeChiralityStar_sq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L69 [advisory] `local-hypothesis-injection` in `theorem hodgeChiralityStar_sq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L71 [advisory] `local-hypothesis-injection` in `theorem hodgeChiralityStar_sq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L73 [advisory] `local-hypothesis-injection` in `theorem hodgeChiralityStar_sq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L75 [advisory] `local-hypothesis-injection` in `theorem hodgeChiralityStar_sq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L86 [soft] `skeletal-proof` in `theorem hodgeChiralityStar_mul_hodgeSD` — proof appears to close via minimal tactic one-liner
  - L91 [advisory] `local-hypothesis-injection` in `theorem hodgeChiralityStar_mul_hodgeSD` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L93 [advisory] `local-hypothesis-injection` in `theorem hodgeChiralityStar_mul_hodgeSD` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L101 [soft] `skeletal-proof` in `theorem hodgeSD_mul_hodgeChiralityStar` — proof appears to close via minimal tactic one-liner
  - L106 [advisory] `local-hypothesis-injection` in `theorem hodgeSD_mul_hodgeChiralityStar` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L108 [advisory] `local-hypothesis-injection` in `theorem hodgeSD_mul_hodgeChiralityStar` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L116 [soft] `skeletal-proof` in `theorem hodgeChiralityStar_mul_hodgeASD` — proof appears to close via minimal tactic one-liner
  - L121 [advisory] `local-hypothesis-injection` in `theorem hodgeChiralityStar_mul_hodgeASD` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L123 [advisory] `local-hypothesis-injection` in `theorem hodgeChiralityStar_mul_hodgeASD` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L131 [soft] `skeletal-proof` in `theorem hodgeASD_mul_hodgeChiralityStar` — proof appears to close via minimal tactic one-liner
  - L136 [advisory] `local-hypothesis-injection` in `theorem hodgeASD_mul_hodgeChiralityStar` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L138 [advisory] `local-hypothesis-injection` in `theorem hodgeASD_mul_hodgeChiralityStar` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L157 [soft] `law-field-locker` in `structure-field DrazinMPChiralHodgeConeBridge.Dirac_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L164 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L231 [soft] `skeletal-proof` in `theorem dirac_square_commutes_hodgeChiralityStar` — proof appears to close via minimal tactic one-liner

