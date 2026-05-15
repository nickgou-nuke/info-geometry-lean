# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:17.617039+00:00`
Root: `lean/InfoGeometry/Canonical/IBFrozenJaynes.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **2**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBFrozenJaynes.lean` | `advisory` | 10 | 0 | 2 | 6 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBFrozenJaynes.lean`
- module: `InfoGeometry.Canonical.IBFrozenJaynes`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [advisory] `existential-packaging` in `lemma frozenSliceJaynes_partition_one_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L66 [soft] `skeletal-proof` in `lemma frozenSlice_partition_eq_baScoreFrozen_tsum_toReal` — proof appears to close via minimal tactic one-liner
  - L98 [soft] `skeletal-proof` in `lemma frozenSlice_logPartition_eq_logPartitionFrozen` — proof appears to close via minimal tactic one-liner
  - L110 [advisory] `local-hypothesis-injection` in `lemma frozenSlice_logPartition_eq_logPartitionFrozen` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L232 [advisory] `local-hypothesis-injection` in `lemma local_free_energy_identity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L237 [advisory] `local-hypothesis-injection` in `lemma local_free_energy_identity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L238 [advisory] `local-hypothesis-injection` in `lemma local_free_energy_identity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

