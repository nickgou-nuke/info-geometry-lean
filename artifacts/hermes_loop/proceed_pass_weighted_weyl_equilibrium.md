# Proceed pass: weighted Weyl equilibrium bridge

This pass continued the infinite operatorial hypothesis reduction lane.

## New theorem added
File:
- `lean/InfoGeometry/Canonical/WeightedWeylNormalizationBridge.lean`

New theorem:
- `densityWeightLiftedReadout_pair_eq_weighted_phaseAxisReadout_of_equilibriumSeed`

## Meaning
Given:
- `hEq : GibbsSouriauEquilibriumSeed (E := E) P ψ A`
- arbitrary weight `w : ℝ`

The theorem proves that the weighted density-lifted readout packet is exactly
the explicit weighted phase-axis response:

- the zero-weight part vanishes by equilibrium,
- only the `w • [densityWeightPhaseAxis, A]` contribution remains.

This is an infinite doubled-carrier theorem. No finite matrix/coordinate toy is
used.

## Constructive chain now owned
- `GibbsSouriauEquilibriumSeed`
  -> `comparisonReadout_pair_eq_zero_of_equilibriumSeed`
  -> `densityWeightLiftedReadout_zero_pair_eq_zero_of_equilibriumSeed`
  -> `densityWeightLiftedReadout_pair_eq_weighted_phaseAxisReadout_of_equilibriumSeed`

So the equilibrium packet now controls not only the ordinary readout, but also
its weighted Weyl/density lift at arbitrary weight.

## Verification
- `lake build InfoGeometry.Canonical.WeightedWeylNormalizationBridge` ✅
- manual test harness:
  - `tests/test_density_weight_equilibrium_bridge_theorems.py` ✅
  - `tests/test_weighted_weyl_equilibrium_bridge_theorems.py` ✅
  - `tests/test_souriau_conformal_equilibrium_seed.py` ✅
  - `tests/test_souriau_thermodynamic_readout_seed_bridge.py` ✅

## Frontier after this pass
Still open and honest:
- `GibbsSouriauEquilibriumSeed -> RNEntropySourcesMongeAmpere ...`
- `GibbsSouriauEquilibriumSeed -> IncompressibleMongeAmpere ...`
- `GibbsSouriauEquilibriumSeed -> CI.chiralScale = kahlerPotentialRN ...`

But the operatorial weighted-response lane is now tighter: equilibrium reduces
all weighted readout structure to the explicit phase-axis commutator term.
That is a real reduction target for the next owner theorem toward density/volume
control.
