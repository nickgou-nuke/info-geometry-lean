# Repo-Native Plug Candidates

This report is a derived triage map for the current ownerless sockets.
It ranks the highest-impact debt first and points each socket at the closest
existing repo owner / bridge surface before any literature search.

## Root-first plug order

The ledger now starts from the roots: lowest direct dependency depth first,
then local bridge density, then fan-out.  The first pass is therefore not the
MBK crown family; it is the low-depth root corridor that can be plugged from
existing repo owners and bridge wrappers.

Suggested repo-native plug order:

1. `MellinInversionParitySocket`
   - candidate bridge: `Canonical.PrimeCl11MellinHurwitzBridge.PrimeCl11MellinHurwitzOwnerTarget`
2. `InfoGeometry.Arithmetic.SplitMajoranaPrimon.InfiniteEulerProductZetaBridge`
   - candidate owner surfaces: `PrimeWittenCharacter`, `PrimeMajoranaPfaffian`, `SplitMajoranaPrimon`
3. `InfoGeometry.Canonical.CantorCliffordMellinPrimeGasBridge.ZetaZeroSocket`
   - candidate owner surfaces: `CantorTiltSwitchCliffordBridge`, `PrimeWittenCharacterCalibration`
4. `InfoGeometry.Canonical.PrimonTFDKreinMobiusBridge.WitnessGatedZetaZeroSocket`
   - candidate owner surfaces: `PrimonDoubledKreinKMSSocket`, `PrimonFreeEnergyRelativeTrace`
5. `InfoGeometry.Canonical.RadioactivePoissonBitStream.RadioactiveSpinorSocket`
   - candidate owner surfaces: `PrimeMajoranaCAR`, `PrimeCantorTiltFockRepresentation`
6. `InfoGeometry.Canonical.PrimonTFDKreinMobiusBridge.TypeIIIModularPrimonSocket`
   - candidate owner surfaces: `PrimonKreinKMS`, `PrimeSuperalgebraReadback`
7. `MobiusFreeEnergyInversionSocket`
   - local theorem: `freeEnergy_determinantLineInversion_eq_log`
8. `RelativeTraceSignatureSocket`
   - local theorem: `relativeTrace_formula`
   - local theorem: `fermionic_primeOrbit_minusSign`
9. `FiveGradedMobiusBalanceSocket`
   - candidate owner surface: `InfoGeometry.OperatorAlgebra.FiveGradedDefectAbsorption.FiveGradeDefectAbsorptionOwnerTarget`
10. `InfoGeometry.Canonical.ChiralDiracHomologyBridge.ChiralComplexSocket`
    - candidate owner surfaces: `RealIncidenceHomologyBridge`, `ChiralHodgeHomologyCalibration`

These sockets are the clearest "search repo first" targets on the root pass.
The MBK analytic family is still important, but it is now a later crown pass
after the roots have been checked and bridged.

## Free-energy / trace pocket

`Arithmetic/PrimonFreeEnergyRelativeTrace.lean` already contains the main
finite and witness-gated surfaces.

Suggested repo-native plug order:

1. `WeylMobiusDeterminantInversionSocket`
   - local theorem: `freeEnergy_determinantLineInversion_eq_log`
2. `StableUnstableGibbsChartSocket`
   - local theorem: `stable_gibbs_minimizer`
   - local theorem: `inverted_chart`
3. `RelativeTraceSignatureSocket`
   - local theorem: `relativeTrace_formula`
   - local theorem: `fermionic_primeOrbit_minusSign`
   - local theorem: `relativeTrace_matches_explicitFormula`
4. `MobiusFreeEnergyInversionSocket`
   - local theorem: `majorana_inverseZeta`
   - local theorem: `freeEnergy_logDual`
5. `MellinInversionParitySocket`
   - candidate bridge: `Canonical.PrimeCl11MellinHurwitzBridge.PrimeCl11MellinHurwitzOwnerTarget`
6. `KLEquilibriumSocket`
   - candidate owner surface: `InfoGeometry.OperatorAlgebra.KapustinWittenDualitySocket.OperatorSDualityOwnerTarget`
7. `FiveGradedMobiusBalanceSocket`
   - candidate owner surface: `InfoGeometry.OperatorAlgebra.FiveGradedDefectAbsorption.FiveGradeDefectAbsorptionOwnerTarget`

These sockets are already partially discharged by local witness theorems.  The
repo-native plug is to consolidate them into a file-level owner target in the
same file family, then route any remaining gaps to the referenced owner surfaces.

## Krein / chiral / Drazin pockets

`Arithmetic/PrimonKreinKMS.lean`, `Canonical/ChiralDiracHomologyBridge.lean`,
and `Canonical/DrazinFierzBridge.lean` already expose the local statements
needed to tighten their file-level bridge surfaces.

Suggested repo-native plug order:

1. `NormalizableArithmeticKMSSocket`
2. `RealDoubledKreinKMSSocket`
3. `PrimonDoubledKreinKMSSocket`
4. `ChiralComplexSocket`
5. `ChiralHodgeDiracSocket`
6. `ExpectationOnlyFierzSocket`
7. `ExpectationBirkhoffSocket`
8. `HurwitzToPermutationSocket`

The repo-native owner/bridge search should first reuse:
- `PrimonKreinKMS` local KMS theorems and doubled-Krein readbacks
- `ChiralHodgeHomologyCalibration` and `RealIncidenceHomologyBridge`
- `DrazinCentralizerErlangen` and `DrazinSupergradedWeylSocket`

## Search order

For the current debt, the search order should be:

1. same file witness theorems
2. same family calibration / bridge wrappers
3. nearby owner surfaces in `lean/InfoGeometry/Canonical`
4. only then literature or external formal systems

This keeps the ledger honest: a socket is not handed to literature until the
repo has been searched for a native owner or bridge path first.
