import proofs.ModularTimeDeRhamBridge

/-!
# Modular parabolic time bridge

Thin capstone/alias layer for the statement:

`dlog Q around the forbidden light cone is the modular automorphism derivation,
 and its finite clock is parabolic affine time`.

This file intentionally reuses `ModularTimeDeRhamBridge` as the proof kernel and
adds a naming layer matching the final physical slogan.  The analytic equality
with Tomita--Takesaki/Bisognano--Wichmann/de Rham residue theory remains a
data interface for the identification, while the finite `g₀` and
parabolic-clock facts are proved.
-/

noncomputable section

namespace ModularParabolicTimeBridge

open TKKJordanPairData.Legacy
open ChemicalPotentialDeRhamG0Bridge
open ThermodynamicTKKBridge
open ModularTimeDeRhamBridge

/-- Final-slogan alias for the data identifying the forbidden-cone
de Rham class with the modular derivation and parabolic clock. -/
abbrev ModularParabolicTimeIdentification := DeRhamModularTimeIdentification

/-- Final-slogan alias for the parabolic shear clock. -/
abbrev ParabolicTimeClock := ParabolicShearClock

/-- The core theorem under the final name: the forbidden-cone de Rham generator
is identified with the modular derivation; the finite kernel proves `δ ∈ g₀`, grade
preservation, additive parabolic clocking, and affine log-clock translation. -/
theorem deRham_is_modular_parabolic_time_derivation
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (C : AbstractDeRhamComplex)
    (I : ModularParabolicTimeIdentification C R G)
    (F : BogoliubovWeylChemicalPotential.BogoliubovInertialFrame)
    (a : AffineSimplexParameter)
    (P Q : ParabolicTimeClock)
    (hId : I.deRhamGeneratorIsModularDerivation)
    (hClock : I.clocksParabolicTime)
    (hResidue : I.residueMonodromyPeriod)
    (hThermal : I.connesRovelliThermalTime)
    (hBW : I.bisognanoWichmannLightConeFlow) :
    I.modularDerivation.derivationGenerator ∈ G.grade TKKGrade.z0 ∧
    (∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
      ⁅I.modularDerivation.derivationGenerator, x⁆ ∈ G.grade i) ∧
    I.contractionClock = I.kmsResiduePeriod ∧
    I.deRhamGeneratorIsModularDerivation ∧
    I.clocksParabolicTime ∧
    I.residueMonodromyPeriod ∧
    I.connesRovelliThermalTime ∧
    I.bisognanoWichmannLightConeFlow ∧
    (P.comp Q).τ = P.τ + Q.τ ∧
    BogoliubovWeylChemicalPotential.frameWeylLogClock
        { F with θ := F.θ + affineLogQ a } =
      BogoliubovWeylChemicalPotential.frameWeylLogClock F + affineLogQ a := by
  rcases modular_time_clocks_deRham_forbidden_cone G C I F a P Q
      hId hClock hResidue hThermal hBW with
    ⟨hg0, hpres, hperiod, hId', hClock', hResidue', hThermal', hBW', hPQ,
      _hN2, _hTickAdd, _hTickInv, hAffine⟩
  constructor
  · simpa using hg0
  constructor
  · simpa using hpres
  constructor
  · simpa using hperiod
  constructor
  · simpa using hId'
  constructor
  · simpa using hClock'
  constructor
  · simpa using hResidue'
  constructor
  · simpa using hThermal'
  constructor
  · simpa using hBW'
  constructor
  · rw [hPQ]
  · simpa using hAffine

end ModularParabolicTimeBridge

end noncomputable section
