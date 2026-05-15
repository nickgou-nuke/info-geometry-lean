# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:41.533472+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/Blocks.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **19**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/Blocks.lean` | `advisory` | 39 | 0 | 19 | 1 | 20 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/Blocks.lean`
- module: `InfoGeometry.SuperMetriplectic.Blocks`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `simp-law-injection` in `simp-declaration dual_dual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `law-field-locker` in `structure-field TKKOnsagerMatrix.entry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field TKKOnsagerMatrix.reciprocal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field CocycleModifiedHessianEntry.hessian_eq_covariance_add_cocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field WeylScaledOnsagerEntry.new_eq_factor_mul_old` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L135 [soft] `law-field-locker` in `structure-field HestenesChiralConeCrossResponse.inChiralCone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L136 [soft] `law-field-locker` in `structure-field HestenesChiralConeCrossResponse.charge_eq_rotation_add_boost` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L140 [soft] `law-field-locker` in `structure-field HestenesChiralConeCrossResponse.p_charge_commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field HestenesChiralConeCrossResponse.lieContribution_eq_zero_of_commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L143 [soft] `law-field-locker` in `structure-field HestenesChiralConeCrossResponse.total_eq_lie_plus_covariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [soft] `law-field-locker` in `structure-field ConformalOnsagerBlock.bracket_P_K_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L204 [soft] `law-field-locker` in `structure-field ConformalOnsagerBlock.reversiblePK_eq_dilation_lorentz_moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L206 [soft] `law-field-locker` in `structure-field ConformalOnsagerBlock.totalPK_eq_reversible_plus_covariance_plus_cocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L260 [soft] `law-field-locker` in `structure-field ConformalPKMetriplecticSplit.dissipativePK_eq_covariance_plus_cocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L262 [soft] `law-field-locker` in `structure-field ConformalPKMetriplecticSplit.totalPK_eq_reversible_plus_dissipative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L306 [soft] `law-field-locker` in `structure-field ConformalBulkViscosityPacket.trace_eq_anomaly` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L307 [soft] `law-field-locker` in `structure-field ConformalBulkViscosityPacket.bulkViscosity_eq_zero_of_trace_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L348 [soft] `law-field-locker` in `structure-field PerfectCFTDissipationGate.trace_eq_anomaly` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L349 [soft] `law-field-locker` in `structure-field PerfectCFTDissipationGate.dissipative_blocks_vanish_of_trace_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

