# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:31.176071+00:00`
Root: `lean/InfoGeometry/External/Virasoro/CyclicTripleSum.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **9**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/CyclicTripleSum.lean` | `advisory` | 19 | 0 | 9 | 1 | 10 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/CyclicTripleSum.lean`
- module: `InfoGeometry.External.Virasoro.CyclicTripleSum`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L57 [soft] `skeletal-proof` in `lemma cyclicTripleSum_apply` — proof appears to close via minimal tactic one-liner
  - L62 [soft] `skeletal-proof` in `lemma cyclicTripleSum_cyclic` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `lemma cyclicTripleSum_map_add_fst_of_map_add` — proof appears to close via minimal tactic one-liner
  - L78 [soft] `skeletal-proof` in `lemma cyclicTripleSum_map_add_snd_of_map_add` — proof appears to close via minimal tactic one-liner
  - L85 [soft] `skeletal-proof` in `lemma cyclicTripleSum_map_smul_fst_of_map_smul` — proof appears to close via minimal tactic one-liner
  - L92 [soft] `skeletal-proof` in `lemma cyclicTripleSum_map_smul_snd_of_map_smul` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `skeletal-proof` in `lemma cyclicTripleSum_map_add_of_bilin` — proof appears to close via minimal tactic one-liner
  - L129 [soft] `skeletal-proof` in `lemma cyclicTripleSum_map_smul_of_bilin` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `skeletal-proof` in `lemma cyclicTripleSumHom_apply` — proof appears to close via minimal tactic one-liner

