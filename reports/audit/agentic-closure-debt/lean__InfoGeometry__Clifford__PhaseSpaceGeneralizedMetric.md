# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:18.795118+00:00`
Root: `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **16**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean` | `advisory` | 42 | 0 | 16 | 10 | 26 |

## Findings by file

### `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
- module: `InfoGeometry.Clifford.PhaseSpaceGeneralizedMetric`
- status: `advisory`
- debt_score: `42`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `structure-field MetricDatum.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field BFieldDatum.twist` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field BFieldDatum.skew` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `simp-law-injection` in `simp-declaration zero_twist` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L175 [soft] `simp-law-injection` in `simp-declaration gForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L184 [soft] `simp-law-injection` in `simp-declaration bForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L193 [soft] `simp-law-injection` in `simp-declaration basePolarization_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L197 [soft] `simp-law-injection` in `simp-declaration bTransform_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L201 [soft] `simp-law-injection` in `simp-declaration bTransformInv_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L235 [soft] `simp-law-injection` in `simp-declaration polarization_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L246 [soft] `simp-law-injection` in `simp-declaration generalizedMetricForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L251 [soft] `simp-law-injection` in `simp-declaration generalizedMetricQuadraticForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L256 [soft] `simp-law-injection` in `simp-declaration canonicalNeutralBilin_symm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L305 [advisory] `local-hypothesis-injection` in `def minusProjector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L307 [advisory] `local-hypothesis-injection` in `def minusProjector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L333 [soft] `simp-law-injection` in `simp-declaration ofMetric_polarization` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L343 [soft] `simp-law-injection` in `simp-declaration generalizedMetricForm_ofMetric_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L349 [advisory] `local-hypothesis-injection` in `def ofMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L352 [soft] `simp-law-injection` in `simp-declaration generalizedMetricForm_apply_explicit` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L361 [advisory] `local-hypothesis-injection` in `def ofMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L373 [advisory] `local-hypothesis-injection` in `def ofMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L375 [advisory] `local-hypothesis-injection` in `def ofMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L377 [advisory] `local-hypothesis-injection` in `def ofMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L384 [advisory] `local-hypothesis-injection` in `def ofMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L413 [advisory] `local-hypothesis-injection` in `def ofMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

