# Hypothesis Debt Index

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../README.md), [docs/README.md](../docs/README.md), [docs/CODEBASE_STATUS.md](../docs/CODEBASE_STATUS.md)

- generated_at: `2026-04-26T07:05:57+00:00`
- declarations_scored: `26`
- files_scored: `2`
- graph_anchor_coverage: `26/26` (1.0)
- nonexported_included: `False`

## Target Files

- `lean/InfoGeometry/Canonical/MasterSynthesis.lean`
- `lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean`
- `lean/InfoGeometry/Canonical/BekensteinBound.lean`

## File Summary

| file | decl_count | lexical_total | lexical_mean | lexical_max | hybrid_total | hybrid_mean | hybrid_max |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BekensteinBound.lean` | 21 | 24.0 | 1.143 | 2.0 | 22.578 | 1.075 | 4.4 |
| `lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean` | 5 | 35.0 | 7.0 | 10.0 | 77.0 | 15.4 | 22.0 |

## Top Debt Surfaces

| rank | hybrid | lexical | visibility | graph_role | theorem_users | value_users | type_users | rep_layer | declaration | location | h_names | bridge_types | prop_types | predicates |
| ---: | ---: | ---: | --- | --- | ---: | ---: | ---: | --- | --- | --- | ---: | ---: | ---: | ---: |
| 1 | 22.0 | 10.0 | `public` | `isolated_theorem` | 0 | 0 | 0 | `-` | `logAbsDetMatrix_mul` | `lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean:46` | 2 | 0 | 2 | 0 |
| 2 | 22.0 | 10.0 | `public` | `isolated_theorem` | 0 | 0 | 0 | `-` | `logAbsDetMatrix_kronecker` | `lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean:63` | 2 | 0 | 2 | 0 |
| 3 | 22.0 | 10.0 | `public` | `isolated_theorem` | 0 | 0 | 0 | `-` | `logAbsJacDetCLM_comp` | `lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean:100` | 2 | 0 | 2 | 0 |
| 4 | 11.0 | 5.0 | `public` | `isolated_theorem` | 0 | 0 | 0 | `-` | `log_spectralMongeAmpereDensity_eq_basepointLogVolume` | `lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean:135` | 1 | 0 | 1 | 0 |
| 5 | 4.4 | 2.0 | `public` | `isolated_theorem` | 0 | 0 | 0 | `-` | `topologicalBekensteinBound_of_connesCocycle` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:91` | 0 | 0 | 1 | 0 |
| 6 | 4.4 | 2.0 | `public` | `isolated_theorem` | 0 | 0 | 0 | `-` | `cocycleGeneratorLift_iff_natMatch_of_connesCocycle` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:305` | 0 | 0 | 1 | 0 |
| 7 | 4.4 | 2.0 | `public` | `isolated_theorem` | 0 | 0 | 0 | `-` | `cocycleIncrement_abs_le_trajectoryRNBarrier_of_connesCocycle_generatorLift` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:361` | 0 | 0 | 1 | 0 |
| 8 | 4.4 | 2.0 | `public` | `isolated_theorem` | 0 | 0 | 0 | `-` | `relEnt_drop_nonneg_of_casiniIncrementBridge` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:482` | 0 | 0 | 1 | 0 |
| 9 | 0.715 | 2.0 | `public` | `supported_theorem` | 1 | 1 | 0 | `-` | `cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:214` | 0 | 0 | 1 | 0 |
| 10 | 0.715 | 2.0 | `public` | `supported_theorem` | 1 | 1 | 0 | `-` | `topologicalBekensteinBound_of_connesCocycle_generatorLift_zero` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:414` | 0 | 0 | 1 | 0 |
| 11 | 0.715 | 2.0 | `public` | `supported_theorem` | 1 | 1 | 0 | `-` | `cocycleGeneratorLift_of_casiniIncrementBridge` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:462` | 0 | 0 | 1 | 0 |
| 12 | 0.715 | 2.0 | `public` | `supported_theorem` | 1 | 1 | 0 | `-` | `topologicalBekensteinBound_of_connesCocycle_casiniIncrement` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:497` | 0 | 0 | 1 | 0 |
| 13 | 0.594 | 2.0 | `public` | `supported_theorem` | 2 | 2 | 0 | `-` | `cocycleGeneratorLift_of_cocycleEntropyPotential_match` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:178` | 0 | 0 | 1 | 0 |
| 14 | 0.594 | 2.0 | `public` | `supported_theorem` | 2 | 2 | 0 | `-` | `cocycleEntropyPotential_natMatch_of_connesCocycle_generatorLift` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:284` | 0 | 0 | 1 | 0 |
| 15 | 0.594 | 2.0 | `public` | `supported_theorem` | 2 | 2 | 0 | `-` | `topologicalBekensteinBound_of_connesCocycle_natMatch` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:390` | 0 | 0 | 1 | 0 |
| 16 | 0.336 | 2.0 | `public` | `load_bearing` | 5 | 5 | 0 | `-` | `topologicalBekensteinBound_of_connesCocycle_generatorLift` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:330` | 0 | 0 | 1 | 0 |
| 17 | 0.0 | 0.0 | `public` | `supported_theorem` | 1 | 1 | 0 | `-` | `trajectoryRNBarrier_nonneg` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:25` | 0 | 0 | 0 | 0 |
| 18 | 0.0 | 0.0 | `public` | `supported_theorem` | 2 | 2 | 0 | `-` | `topologicalBekensteinBound_of_sinkhornTrajectory` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:42` | 0 | 0 | 0 | 0 |
| 19 | 0.0 | 0.0 | `public` | `supported_theorem` | 2 | 2 | 0 | `-` | `abs_trajectoryRNGenerator_le_trajectoryRNBarrier` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:65` | 0 | 0 | 0 | 0 |
| 20 | 0.0 | 0.0 | `public` | `supported_theorem` | 1 | 1 | 0 | `-` | `cocycleGeneratorLift_of_trajectoryRNGeneratorPotential` | `lean/InfoGeometry/Canonical/BekensteinBound.lean:147` | 0 | 0 | 0 | 0 |

Lexical hint score: `3*hypothesis_names + 2*prop_types + 4*bridge_types + 1*predicate_types + 0.5*instances + 0.1*implicit`.
Hybrid priority is lexical debt reweighted by DAG-backed structural role and load-bearing score.
Strict graph doctrine: by default, private/protected non-exported declarations are skipped because they are not graph-addressable theorem surfaces.
