# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:30.828537+00:00`
Root: `lean/InfoGeometry/Projective/LogSum.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **1**
- Advisory: **20**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/LogSum.lean` | `advisory` | 22 | 0 | 1 | 20 | 21 |

## Findings by file

### `lean/InfoGeometry/Projective/LogSum.lean`
- module: `InfoGeometry.Projective.LogSum`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L12 [advisory] `existential-packaging` in `theorem logSum_inequality` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L12 [soft] `skeletal-proof` in `theorem logSum_inequality` — proof appears to close via minimal tactic one-liner
  - L25 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L28 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L34 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L39 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L46 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L51 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L56 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L59 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L71 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L76 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L80 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L92 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L95 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L107 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L125 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L131 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L135 [advisory] `local-hypothesis-injection` in `theorem logSum_inequality` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

