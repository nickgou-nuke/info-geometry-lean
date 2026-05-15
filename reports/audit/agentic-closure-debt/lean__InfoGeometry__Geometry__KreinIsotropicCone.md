# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:38.109012+00:00`
Root: `lean/InfoGeometry/Geometry/KreinIsotropicCone.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **10**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/KreinIsotropicCone.lean` | `advisory` | 30 | 0 | 10 | 10 | 20 |

## Findings by file

### `lean/InfoGeometry/Geometry/KreinIsotropicCone.lean`
- module: `InfoGeometry.Geometry.KreinIsotropicCone`
- status: `advisory`
- debt_score: `30`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L25 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.q_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L28 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.q_smul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L69 [soft] `simp-law-injection` in `simp-declaration mem_isotropicCone_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `simp-law-injection` in `simp-declaration mem_strictIsotropicCone_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `simp-law-injection` in `simp-declaration mem_positiveKreinCone_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L87 [soft] `simp-law-injection` in `simp-declaration mem_negativeKreinCone_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `simp-law-injection` in `simp-declaration zero_mem_isotropicCone` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L106 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L154 [advisory] `local-hypothesis-injection` in `theorem positive_not_isotropic` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L155 [advisory] `local-hypothesis-injection` in `theorem positive_not_isotropic` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L164 [advisory] `local-hypothesis-injection` in `theorem negative_not_isotropic` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L165 [advisory] `local-hypothesis-injection` in `theorem negative_not_isotropic` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L169 [advisory] `existential-packaging` in `def SameProjectiveRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L191 [soft] `law-field-locker` in `structure-field DefectMapsToIsotropic.carrierReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L194 [soft] `law-field-locker` in `structure-field DefectMapsToIsotropic.defect_is_isotropic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L206 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L223 [advisory] `existential-packaging` in `def DefectToIsotropicOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

