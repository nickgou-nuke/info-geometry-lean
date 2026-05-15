# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:15.772228+00:00`
Root: `lean/InfoGeometry/Causal/MirrorAlignment.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **3**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Causal/MirrorAlignment.lean` | `advisory` | 19 | 0 | 3 | 13 | 16 |

## Findings by file

### `lean/InfoGeometry/Causal/MirrorAlignment.lean`
- module: `InfoGeometry.Causal.MirrorAlignment`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `skeletal-proof` in `lemma MirrorMismatch_eq_half_complex_i` — proof appears to close via minimal tactic one-liner
  - L28 [soft] `skeletal-proof` in `lemma MirrorMismatch_maps_NullCone` — proof appears to close via minimal tactic one-liner
  - L31 [advisory] `local-hypothesis-injection` in `lemma MirrorMismatch_maps_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L34 [advisory] `local-hypothesis-injection` in `lemma MirrorMismatch_maps_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L36 [advisory] `local-hypothesis-injection` in `lemma MirrorMismatch_maps_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L38 [advisory] `local-hypothesis-injection` in `lemma MirrorMismatch_maps_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L44 [soft] `skeletal-proof` in `theorem MirrorMismatch_ne_zero_on_NullCone` — proof appears to close via minimal tactic one-liner
  - L47 [advisory] `local-hypothesis-injection` in `theorem MirrorMismatch_ne_zero_on_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L53 [advisory] `local-hypothesis-injection` in `theorem MirrorMismatch_ne_zero_on_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L54 [advisory] `local-hypothesis-injection` in `theorem MirrorMismatch_ne_zero_on_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L56 [advisory] `local-hypothesis-injection` in `theorem MirrorMismatch_ne_zero_on_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L58 [advisory] `local-hypothesis-injection` in `theorem MirrorMismatch_ne_zero_on_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L61 [advisory] `local-hypothesis-injection` in `theorem MirrorMismatch_ne_zero_on_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L62 [advisory] `local-hypothesis-injection` in `theorem MirrorMismatch_ne_zero_on_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L64 [advisory] `local-hypothesis-injection` in `theorem MirrorMismatch_ne_zero_on_NullCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

