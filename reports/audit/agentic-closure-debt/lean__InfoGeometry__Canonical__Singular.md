# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:55.351344+00:00`
Root: `lean/InfoGeometry/Canonical/Singular.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **49**
- Hard: **0**
- Soft: **7**
- Advisory: **42**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/Singular.lean` | `advisory` | 56 | 0 | 7 | 42 | 49 |

## Findings by file

### `lean/InfoGeometry/Canonical/Singular.lean`
- module: `InfoGeometry.Canonical.Singular`
- status: `advisory`
- debt_score: `56`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L59 [advisory] `existential-packaging` in `theorem exists_moorePenroseInverse_of_isUnit` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L77 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_isUnit` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L89 [advisory] `existential-packaging` in `theorem exists_moorePenroseInverse_of_selfAdjoint_idempotent` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L89 [soft] `skeletal-proof` in `theorem exists_moorePenroseInverse_of_selfAdjoint_idempotent` — proof appears to close via minimal tactic one-liner
  - L115 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_idempotent` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L115 [soft] `skeletal-proof` in `theorem exists_drazinInverse_of_idempotent` — proof appears to close via minimal tactic one-liner
  - L137 [advisory] `existential-packaging` in `theorem exists_regularization_pair_of_selfAdjoint_idempotent` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L137 [soft] `skeletal-proof` in `theorem exists_regularization_pair_of_selfAdjoint_idempotent` — proof appears to close via minimal tactic one-liner
  - L176 [advisory] `existential-packaging` in `theorem exists_regularization_pair_of_isUnit` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L189 [soft] `simp-law-injection` in `simp-declaration EinsteinAnomaly_eq_zero_of_regularization_pair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L197 [soft] `simp-law-injection` in `simp-declaration EinsteinAnomaly_eq_zero_of_selfAdjoint_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L215 [advisory] `existential-packaging` in `theorem exists_moorePenroseInverse_endomorphism_of_isUnit` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L225 [advisory] `existential-packaging` in `theorem exists_drazinInverse_endomorphism_of_isUnit` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L237 [advisory] `existential-packaging` in `theorem exists_drazinInverse_global` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L237 [soft] `skeletal-proof` in `theorem exists_drazinInverse_global` — proof appears to close via minimal tactic one-liner
  - L252 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L254 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L256 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L265 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L271 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L274 [advisory] `local-hypothesis-injection` in `theorem exists_drazinInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L278 [advisory] `existential-packaging` in `theorem exists_moorePenroseInverse_global` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L278 [soft] `skeletal-proof` in `theorem exists_moorePenroseInverse_global` — proof appears to close via minimal tactic one-liner
  - L306 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L316 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L319 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L322 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L329 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L331 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L334 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L356 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L360 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L364 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L368 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L381 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L386 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L393 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L396 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L399 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L416 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L420 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L424 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L432 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L435 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L443 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L445 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L454 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L456 [advisory] `local-hypothesis-injection` in `theorem exists_moorePenroseInverse_global` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

