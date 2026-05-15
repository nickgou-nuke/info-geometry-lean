# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:39.972326+00:00`
Root: `lean/InfoGeometry/Singular/MoorePenrose.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **2**
- Advisory: **20**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Singular/MoorePenrose.lean` | `advisory` | 24 | 0 | 2 | 20 | 22 |

## Findings by file

### `lean/InfoGeometry/Singular/MoorePenrose.lean`
- module: `InfoGeometry.Singular.MoorePenrose`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L80 [soft] `skeletal-proof` in `theorem MoorePenrose_unique` — proof appears to close via minimal tactic one-liner
  - L85 [advisory] `local-hypothesis-injection` in `theorem MoorePenrose_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L99 [advisory] `local-hypothesis-injection` in `theorem MoorePenrose_unique` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L148 [soft] `skeletal-proof` in `theorem mpRestricted_injective` — proof appears to close via minimal tactic one-liner
  - L153 [advisory] `local-hypothesis-injection` in `theorem mpRestricted_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L159 [advisory] `local-hypothesis-injection` in `theorem mpRestricted_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L173 [advisory] `local-hypothesis-injection` in `theorem mpRestricted_surjective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L175 [advisory] `local-hypothesis-injection` in `theorem mpRestricted_surjective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L177 [advisory] `local-hypothesis-injection` in `theorem mpRestricted_surjective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L220 [advisory] `local-hypothesis-injection` in `theorem isMoorePenroseInverse_moorePenroseInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L224 [advisory] `local-hypothesis-injection` in `theorem isMoorePenroseInverse_moorePenroseInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L225 [advisory] `local-hypothesis-injection` in `theorem isMoorePenroseInverse_moorePenroseInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L231 [advisory] `local-hypothesis-injection` in `theorem isMoorePenroseInverse_moorePenroseInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L235 [advisory] `local-hypothesis-injection` in `theorem isMoorePenroseInverse_moorePenroseInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L238 [advisory] `local-hypothesis-injection` in `theorem isMoorePenroseInverse_moorePenroseInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L240 [advisory] `local-hypothesis-injection` in `theorem isMoorePenroseInverse_moorePenroseInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L249 [advisory] `local-hypothesis-injection` in `theorem isMoorePenroseInverse_moorePenroseInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L252 [advisory] `local-hypothesis-injection` in `theorem isMoorePenroseInverse_moorePenroseInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L257 [advisory] `local-hypothesis-injection` in `theorem isMoorePenroseInverse_moorePenroseInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L286 [advisory] `existential-packaging` in `theorem exists_moorePenroseInverse_of_closedRange` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

