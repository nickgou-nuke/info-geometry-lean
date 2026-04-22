# Proceed pass: weighted Weyl phase-axis commutation closure

This pass sharpened the infinite operatorial weighted-readout lane.

## New theorem added
File:
- `lean/InfoGeometry/Canonical/WeightedWeylNormalizationBridge.lean`

New theorem:
- `densityWeightLiftedReadout_pair_eq_zero_of_equilibriumSeed_of_commute_phaseAxis`

## Meaning
Given:
- `hEq : GibbsSouriauEquilibriumSeed (E := E) P ψ A`
- `hComm : Commute A (densityWeightPhaseAxis (E := E))`
- arbitrary weight `w : ℝ`

The theorem proves:
- the full weighted density-lifted readout packet is `(0, 0)`.

Constructive route:
1. equilibrium kills the zero-weight packet via
   `densityWeightLiftedReadout_zero_pair_eq_zero_of_equilibriumSeed`
2. the weighted packet is the explicit phase-axis correction via
   `densityWeightLiftedReadout_pair_eq_weighted_phaseAxisReadout_of_equilibriumSeed`
3. phase-axis commutation forces the correction commutator to vanish
4. therefore the full weighted packet vanishes

This is still fully on the doubled carrier and uses no finite response matrix.

## Verification
- `lake build InfoGeometry.Canonical.WeightedWeylNormalizationBridge` ✅
- manual harness:
  - `tests/test_density_weight_equilibrium_bridge_theorems.py` ✅
  - `tests/test_weighted_weyl_equilibrium_bridge_theorems.py` ✅
  - `tests/test_souriau_conformal_equilibrium_seed.py` ✅
  - `tests/test_souriau_thermodynamic_readout_seed_bridge.py` ✅

## Frontier after this pass
The weighted operatorial lane is now reduced to a precise closure point:
- if equilibrium holds and the observable commutes with the density-weight phase axis,
  then all weighted metric/phase readout vanishes.

Still honestly open:
- deriving the required phase-axis commutation witness from the Souriau
  equilibrium lane itself
- deriving RN entropy source / incompressibility from Souriau equilibrium
- deriving `CI.chiralScale = kahlerPotentialRN ...` from Souriau equilibrium

So the next honest bridge target is now even more explicit:
- equilibrium/readout stationarity -> phase-axis commutation, or
- equilibrium/readout stationarity -> RN/density control directly.
