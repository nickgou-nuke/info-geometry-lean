# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:24.588553+00:00`
Root: `lean/InfoGeometry/Core/MajoranaLiftPacket.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **11**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Core/MajoranaLiftPacket.lean` | `advisory` | 26 | 0 | 11 | 4 | 15 |

## Findings by file

### `lean/InfoGeometry/Core/MajoranaLiftPacket.lean`
- module: `InfoGeometry.Core.MajoranaLiftPacket`
- status: `advisory`
- debt_score: `26`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L40 [soft] `law-field-locker` in `structure-field MajoranaLiftPacket.hJ_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field MajoranaLiftPacket.hEps_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field MajoranaLiftPacket.hJ_eps_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field MajoranaLiftPacket.hK_eq_J_comp_eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L46 [soft] `section-law-variable` in `variable P` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L71 [soft] `simp-law-injection` in `simp-declaration canonicalMajoranaLiftPacket_J_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L73 [soft] `skeletal-proof` in `theorem canonicalMajoranaLiftPacket_J_eq_modular_j` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `simp-law-injection` in `simp-declaration canonicalMajoranaLiftPacket_eps_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `skeletal-proof` in `theorem canonicalMajoranaLiftPacket_eps_eq_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `simp-law-injection` in `simp-declaration canonicalMajoranaLiftPacket_K_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `skeletal-proof` in `theorem canonicalMajoranaLiftPacket_K_eq_complex_i` — proof appears to close via minimal tactic one-liner

