# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:40.265191+00:00`
Root: `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **3**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean` | `advisory` | 16 | 0 | 3 | 10 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean`
- module: `InfoGeometry.Canonical.ArnoldMajoranaNetwork`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L66 [soft] `skeletal-proof` in `theorem expert_apply_mem_transportWeylPlus_of_commutes_transportJ` — proof appears to close via minimal tactic one-liner
  - L128 [soft] `skeletal-proof` in `theorem expert_apply_mem_transportWeylMinus_of_commutes_transportJ_and_odd` — proof appears to close via minimal tactic one-liner
  - L204 [advisory] `local-hypothesis-injection` in `theorem arnoldNetwork_preserves_base` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L324 [advisory] `local-hypothesis-injection` in `theorem expert_apply_mem_ker_of_clm_commutes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L414 [advisory] `existential-packaging` in `theorem arnoldNetworkOutput_eq_of_experts_fix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L414 [soft] `skeletal-proof` in `theorem arnoldNetworkOutput_eq_of_experts_fix` — proof appears to close via minimal tactic one-liner
  - L442 [advisory] `existential-packaging` in `theorem arnoldNetwork_preserves_transportWeylPlus_nonzero_ker_of_experts_fix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L472 [advisory] `existential-packaging` in `theorem arnoldNetwork_preserves_transportWeylMinus_nonzero_ker_of_experts_fix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L502 [advisory] `existential-packaging` in `theorem exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_weylZeroModePair` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L546 [advisory] `existential-packaging` in `theorem exists_network_fixed_transportWeylMinus_nonzero_ker_of_experts_fix_of_weylZeroModePair` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L590 [advisory] `existential-packaging` in `theorem exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L631 [advisory] `existential-packaging` in `theorem exists_network_fixed_transportWeylMinus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

