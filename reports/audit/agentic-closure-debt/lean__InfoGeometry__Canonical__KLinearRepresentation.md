# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:22.648588+00:00`
Root: `lean/InfoGeometry/Canonical/KLinearRepresentation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **14**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KLinearRepresentation.lean` | `advisory` | 35 | 0 | 14 | 7 | 21 |

## Findings by file

### `lean/InfoGeometry/Canonical/KLinearRepresentation.lean`
- module: `InfoGeometry.Canonical.KLinearRepresentation`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `simp-law-injection` in `simp-declaration kLinearPart_add_kAntilinearPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `simp-law-injection` in `simp-declaration id_isKLinear` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration K_isKLinear` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `simp-law-injection` in `simp-declaration J_isKAntilinear` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `simp-law-injection` in `simp-declaration eps_isKAntilinear` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `skeletal-proof` in `lemma kConjugate_comp_K` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `skeletal-proof` in `lemma K_comp_kConjugate` — proof appears to close via minimal tactic one-liner
  - L108 [soft] `skeletal-proof` in `lemma neg_kConjugate_comp_K` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `skeletal-proof` in `lemma neg_K_comp_kConjugate` — proof appears to close via minimal tactic one-liner
  - L118 [soft] `skeletal-proof` in `theorem kLinearPart_isKLinear` — proof appears to close via minimal tactic one-liner
  - L124 [advisory] `local-hypothesis-injection` in `theorem kLinearPart_isKLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L126 [advisory] `local-hypothesis-injection` in `theorem kLinearPart_isKLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L128 [advisory] `local-hypothesis-injection` in `theorem kLinearPart_isKLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L146 [soft] `skeletal-proof` in `theorem kAntilinearPart_isKAntilinear` — proof appears to close via minimal tactic one-liner
  - L152 [advisory] `local-hypothesis-injection` in `theorem kAntilinearPart_isKAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L154 [advisory] `local-hypothesis-injection` in `theorem kAntilinearPart_isKAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L156 [advisory] `local-hypothesis-injection` in `theorem kAntilinearPart_isKAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L181 [soft] `law-field-locker` in `structure-field PolarizedDecomposition.lin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L182 [soft] `law-field-locker` in `structure-field PolarizedDecomposition.anti` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L185 [soft] `law-field-locker` in `structure-field PolarizedDecomposition.h_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

