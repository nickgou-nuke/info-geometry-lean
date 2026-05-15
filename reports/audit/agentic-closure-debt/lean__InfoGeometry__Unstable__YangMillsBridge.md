# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:50.482353+00:00`
Root: `lean/InfoGeometry/Unstable/YangMillsBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **8**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Unstable/YangMillsBridge.lean` | `advisory` | 24 | 0 | 8 | 8 | 16 |

## Findings by file

### `lean/InfoGeometry/Unstable/YangMillsBridge.lean`
- module: `InfoGeometry.Unstable.YangMillsBridge`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L88 [soft] `law-field-locker` in `structure-field SUNGaugeInstantiation.n_ge_two` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [advisory] `existential-packaging` in `structure QFTConstructiveLayer` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L127 [soft] `law-field-locker` in `structure-field QFTConstructiveLayer.reflection_positivity_holds` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L129 [soft] `law-field-locker` in `structure-field QFTConstructiveLayer.osterwalder_schrader_holds` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field QFTConstructiveLayer.wightman_reconstruction_holds` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [advisory] `existential-packaging` in `def ofProofs` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L175 [soft] `skeletal-proof` in `theorem expectationSeedReflectionPositivity_of_jointKernel_commutator_bundle` — proof appears to close via minimal tactic one-liner
  - L208 [soft] `skeletal-proof` in `theorem modularReflectionPositivity_of_positiveTimeVector` — proof appears to close via minimal tactic one-liner
  - L274 [advisory] `existential-packaging` in `def finiteWightmanReconstructionLayer` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L408 [advisory] `local-hypothesis-injection` in `theorem spectralGapFromLogDet_pos_of_coercive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L426 [soft] `law-field-locker` in `structure-field YangMillsMassGapBridge.spectral_gap_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L428 [soft] `law-field-locker` in `structure-field YangMillsMassGapBridge.gamma_le_spectral_gap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L560 [advisory] `bridge-shaped-declaration` in `lemma asymptotic_freedom_of_bridge_rg_model` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L566 [advisory] `bridge-shaped-declaration` in `lemma strict_mass_gap_of_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L576 [advisory] `bridge-shaped-declaration` in `theorem millennium_obligations_of_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

