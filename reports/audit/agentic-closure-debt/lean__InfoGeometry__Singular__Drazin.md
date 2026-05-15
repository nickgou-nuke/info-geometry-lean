# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:39.191862+00:00`
Root: `lean/InfoGeometry/Singular/Drazin.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **50**
- Hard: **0**
- Soft: **9**
- Advisory: **41**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Singular/Drazin.lean` | `advisory` | 59 | 0 | 9 | 41 | 50 |

## Findings by file

### `lean/InfoGeometry/Singular/Drazin.lean`
- module: `InfoGeometry.Singular.Drazin`
- status: `advisory`
- debt_score: `59`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [soft] `skeletal-proof` in `theorem lift` — proof appears to close via minimal tactic one-liner
  - L88 [soft] `skeletal-proof` in `theorem star_isDrazinInverse` — proof appears to close via minimal tactic one-liner
  - L92 [advisory] `local-hypothesis-injection` in `theorem star_isDrazinInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L107 [soft] `skeletal-proof` in `lemma pow_succ_eq_of_idempotent` — proof appears to close via minimal tactic one-liner
  - L122 [soft] `skeletal-proof` in `lemma drazin_projector_idempotent'` — proof appears to close via minimal tactic one-liner
  - L131 [soft] `skeletal-proof` in `lemma mul_pow_eq_drazinProjector_of_pos` — proof appears to close via minimal tactic one-liner
  - L142 [advisory] `local-hypothesis-injection` in `lemma mul_pow_eq_drazinProjector_of_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L150 [soft] `skeletal-proof` in `theorem Drazin_unique` — proof appears to close via minimal tactic one-liner
  - L164 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L166 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L179 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L182 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L188 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L190 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L192 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L206 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L216 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L225 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L228 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L231 [advisory] `local-hypothesis-injection` in `theorem Drazin_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L267 [soft] `skeletal-proof` in `theorem Drazin_star_eq_self_of_selfAdjoint` — proof appears to close via minimal tactic one-liner
  - L281 [soft] `skeletal-proof` in `lemma Drazin_Projector_idempotent` — proof appears to close via minimal tactic one-liner
  - L293 [advisory] `existential-packaging` in `theorem exists_drazinInverse_global` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L293 [soft] `skeletal-proof` in `theorem exists_drazinInverse_global` — proof appears to close via minimal tactic one-liner
  - L312 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L321 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L338 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L351 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L352 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L362 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L364 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L378 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L381 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L391 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L394 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L400 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L414 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L417 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L420 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L436 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L441 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L451 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L460 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L468 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L471 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L477 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L483 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L486 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L539 [advisory] `existential-packaging` in `theorem drazinInverse_unique_any_index` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

