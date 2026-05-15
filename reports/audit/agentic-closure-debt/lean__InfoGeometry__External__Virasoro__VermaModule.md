# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:34.203713+00:00`
Root: `lean/InfoGeometry/External/Virasoro/VermaModule.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **4**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/VermaModule.lean` | `advisory` | 15 | 0 | 4 | 7 | 11 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/VermaModule.lean`
- module: `InfoGeometry.External.Virasoro.VermaModule`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L62 [soft] `simp-law-injection` in `simp-declaration Ring.smulVector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L85 [advisory] `existential-packaging` in `lemma LinearMap.apply_cyclic_of_cyclic_of_surjective` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L163 [soft] `simp-law-injection` in `simp-declaration VermaModule.universalMap_hwVec` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L189 [advisory] `existential-packaging` in `structure IsVermaModule` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L192 [soft] `law-field-locker` in `structure-field IsVermaModule.hwv_prop` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L204 [soft] `simp-law-injection` in `simp-declaration IsVermaModule.universalMap_hwv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L220 [advisory] `existential-packaging` in `lemma VermaModule.isVermaModule` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L230 [advisory] `local-hypothesis-injection` in `lemma VermaModule.isVermaModule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L247 [advisory] `local-hypothesis-injection` in `def IsVermaModule.equiv_of_isVermaModule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L252 [advisory] `local-hypothesis-injection` in `def IsVermaModule.equiv_of_isVermaModule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

