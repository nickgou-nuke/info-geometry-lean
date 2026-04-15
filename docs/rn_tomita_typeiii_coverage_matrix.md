# RN–Tomita–TypeIII Coverage Matrix

## Scope
This document classifies current repo coverage for the Radon–Nikodym / Tomita–Takesaki / Type III / spectral-normal-form lane into:

- `implemented`
- `interface` (compiled skeleton, intentionally partial)
- `missing` (not formalized as an owner theorem surface)

Search footprint used for this pass:

- `120` Lean files in `lean/InfoGeometry` matched the concept query set.
- `29` black-book chapters matched the same concept query set.
- Key owner files were read directly and checked for proof debt markers.

## Coverage Matrix

| Concept | Status | Lean anchors (owner surfaces) | Notes |
|---|---|---|---|
| Classical Radon–Nikodym normal form + uniqueness | implemented | [`lean/InfoGeometry/Measure/RadonNikodymNormalForms.lean`](../lean/InfoGeometry/Measure/RadonNikodymNormalForms.lean): `normalForm_of_absolutelyContinuous`, `absolutelyContinuous_iff_normalForm`, `lebesgueDecomposition_normalForm`, `density_unique_ae`, `rnDeriv_withDensity_eq_ae` | Canonical commutative RN surface is present and theorem-level. |
| Discrete RN normal forms (singletons / PMFs) | implemented | [`lean/InfoGeometry/Measure/DiscreteRN.lean`](../lean/InfoGeometry/Measure/DiscreteRN.lean), [`lean/InfoGeometry/Measure/RadonNikodymNormalForms.lean`](../lean/InfoGeometry/Measure/RadonNikodymNormalForms.lean): `rnDeriv_singleton_eq_mass_ratio`, `rnDeriv_pmf_eq_pointwise_ratio` | Fully integrated into measure umbrella. |
| Scalar RN bridge as multiplicative-to-additive normal form | implemented | [`lean/InfoGeometry/Volume/RadonNikodym.lean`](../lean/InfoGeometry/Volume/RadonNikodym.lean): `HasScalarRNBridge`, `toExactBridge`, `rn_eq_additiveInvariant`, `rn_chain_rule` | Constructive bridge layer, no placeholders. |
| Connes cocycle lane (flow, cocycle law, scalar/log descent) | implemented | [`lean/InfoGeometry/Volume/ConnesCocycle.lean`](../lean/InfoGeometry/Volume/ConnesCocycle.lean): `AdditiveModularFlow`, `IsConnesCocycle`, `flowUnitCocycle_isConnesCocycle`, `scalarCocycle_mul`, `cocycleLogPotential_add` | Real operator-level cocycle package is formalized. |
| Relative modular state-pair core (projective lane) | implemented | [`lean/InfoGeometry/Canonical/RelativeModularCore.lean`](../lean/InfoGeometry/Canonical/RelativeModularCore.lean): `RelativeStatePair`, `compose_logDensity`, `compose_modularPotential`, restriction/reweighting shift theorems | Strong projective owner layer exists. |
| Finite relative modular operator `Δ` + cocycle + volume/log-volume + readouts | implemented | [`lean/InfoGeometry/Canonical/RelativeModularOperator.lean`](../lean/InfoGeometry/Canonical/RelativeModularOperator.lean): `RelativeStatePair.modularOperator`, `relativeModularOperator_cocycle`, `relativeModularVolumeShadow_*`, `relativeModularBerezinian*`, `relativeModularHamiltonianReadout_*` | This is the main finite operator owner surface. |
| Finite `Δ`-primary lift to `K := -log Δ` + commuting spectral package | implemented | [`lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean`](../lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean): `relativeModularHamiltonianOperator`, `relativeModularHamiltonianOperator_cocycle`; [`lean/InfoGeometry/Canonical/RelativeModularCommutingLift.lean`](../lean/InfoGeometry/Canonical/RelativeModularCommutingLift.lean): `relativeModularOperator_mul_comm`, `log_relativeModularOperator_diag_cocycle`, `finite_commuting_lift_package` | Canonical finite lane now has explicit `Δ`-primary ordering and commuting/log-cocycle theorem surface. |
| Tomita modular atom on doubled real carrier (`J, ε, Jε`) | implemented | [`lean/InfoGeometry/Canonical/TomitaTakesaki.lean`](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean): `modularConjugationJ`, `modularSignEpsilon`, `modularComplexI`, involution/anticommutation and flow transport theorems | Explicitly complete as an atom layer. |
| Real modular log-flow core (`δ = log Δ`, flow/additivity/time-reversal) | implemented | [`lean/InfoGeometry/Canonical/RealTomitaCore.lean`](../lean/InfoGeometry/Canonical/RealTomitaCore.lean): `RealModularLogData`, `flow`, `flow_add`, `flow_negLog_eq_time_reverse` | Concrete transport owner layer. |
| Real standard-form orientation contracts (`J`-flip, left/right swap, phase flips) | implemented | [`lean/InfoGeometry/Canonical/TomitaTakesakiRealStandardForm.lean`](../lean/InfoGeometry/Canonical/TomitaTakesakiRealStandardForm.lean): `RealStandardForm`, `flipJ`, `swapLeftRight`, `orientation_equivalence_package` | Compiled and theorem-bearing, focused on gauge/orientation equivalences. |
| Standard-form carrier in full Tomita–Takesaki sense `(M,H,J,P)` | interface | [`lean/InfoGeometry/Canonical/StandardFormCore.lean`](../lean/InfoGeometry/Canonical/StandardFormCore.lean): `StandardFormSeed`, `StandardFormCarrier`, `RelativeModularBridge` | File explicitly states it “stops short of a full Tomita-Takesaki standard-form development.” |
| Type III continuous core (crossed-product level) | interface | [`lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean`](../lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean): `RealTypeIIIModularData`, `RealContinuousCoreInterface` | File explicitly states it “does not construct crossed products internally.” |
| Connes–Araki carrier | interface | [`lean/InfoGeometry/Canonical/ConnesArakiCore.lean`](../lean/InfoGeometry/Canonical/ConnesArakiCore.lean), [`lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`](../lean/InfoGeometry/Canonical/ConnesArakiTomita.lean) | Explicitly framed as “finite Sinkhorn scaffold”; useful but not full operator-algebraic Araki theory. |
| Thermo/modular KL bridge over existing owners | implemented | [`lean/InfoGeometry/Thermo/ModularKLDivergence.lean`](../lean/InfoGeometry/Thermo/ModularKLDivergence.lean) | Packaging layer with proved identities; intentionally “no new ontology.” |
| Finite thermal/KMS models | implemented | [`lean/InfoGeometry/Thermo/FiniteMatrix.lean`](../lean/InfoGeometry/Thermo/FiniteMatrix.lean), [`lean/InfoGeometry/Thermal/FiniteMatrix.lean`](../lean/InfoGeometry/Thermal/FiniteMatrix.lean) | Matrix/diagonal KMS-like realizations are formalized. |
| Full spectral-theorem multiplication model (`L²(μ)`, cyclic subspaces, spectrum decomposition) | missing | No owner module with cyclic-subspace + multiplication representation + spectral-measure decomposition was found in `lean/InfoGeometry` | Current spectral files are finite/operator-lift packaging, not a full Hilbert spectral theorem lane. |
| Full GNS construction layer for C\*-states (repo owner surface) | missing | No dedicated GNS owner module was found in `lean/InfoGeometry` in this pass | Standard-form interfaces exist, but not full GNS/Tomita construction stack. |
| Noncommutative Pedersen–Takesaki affiliated-operator RN theorem stack | missing | No Lean owner theorem surface with Pedersen–Takesaki/Vaes affiliated-operator RN statements found | Appears in black-book analysis text, not yet in Lean owner modules. |

## Evidence That These Are Integrated (Not Isolated)

- Canonical umbrella imports include the modular/RN/TypeIII lane:
  [`lean/InfoGeometry/Canonical/All.lean`](../lean/InfoGeometry/Canonical/All.lean)
  imports `TomitaTakesaki`, `StandardFormCore`, `TomitaTakesakiRealStandardForm`,
  `TypeIIIContinuousCoreReal`, `RelativeModularCore`, `RelativeModularOperator`,
  `RelativeModularHamiltonian`, `RelativeModularCommutingLift`,
  `ConnesArakiCore`, `ConnesArakiTomita`, and `Volume.RadonNikodym`.
- Measure and volume umbrellas include the RN/cocycle owners:
  [`lean/InfoGeometry/Measure/All.lean`](../lean/InfoGeometry/Measure/All.lean),
  [`lean/InfoGeometry/Volume/All.lean`](../lean/InfoGeometry/Volume/All.lean).

## Bottom-Line Verdict

- The repo already contains a substantial, theorem-bearing RN/modular/TypeIII-inspired stack.
- What is still absent is the full classical operator-algebra endpoint:
  spectral multiplication-model theorem layer, full GNS standard-form realization, and Pedersen–Takesaki-style affiliated-operator RN theorem stack.
