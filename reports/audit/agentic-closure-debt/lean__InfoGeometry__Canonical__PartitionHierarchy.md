# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:40.455062+00:00`
Root: `lean/InfoGeometry/Canonical/PartitionHierarchy.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PartitionHierarchy.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/PartitionHierarchy.lean`
- module: `InfoGeometry.Canonical.PartitionHierarchy`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L57 [soft] `simp-law-injection` in `simp-declaration effectivePotential_eq_neg_inv_temp_mul_log_fiberPartition` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L88 [soft] `simp-law-injection` in `simp-declaration grandCanonical_partition_eq_totalPartition` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L93 [soft] `simp-law-injection` in `simp-declaration grandCanonical_partition_eq_trivialFiberPartition` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `simp-law-injection` in `simp-declaration grandCanonical_potential_eq_trivialLogPartitionPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L110 [soft] `simp-law-injection` in `simp-declaration grandCanonical_freeEnergy_eq_trivialEffectivePotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L118 [soft] `simp-law-injection` in `simp-declaration grandCanonical_partitionGC_eq_trivialFiberPartition` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L129 [soft] `simp-law-injection` in `simp-declaration grandCanonical_potentialGC_eq_trivialLogPartitionPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

