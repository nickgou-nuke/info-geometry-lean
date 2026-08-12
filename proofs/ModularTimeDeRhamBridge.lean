import proofs.ModularRadonNikodymJacobianBridge

/-!
# Modular time / de Rham forbidden-cone bridge

Theorem-honest finite layer for the slogan:

`the de Rham generator around the forbidden cone is the modular automorphism
 derivation, and it clocks parabolic time`.

Proved in kernel:

* the modular derivation lives in TKK `g₀` and hence preserves grades;
* the finite affine/Rindler log-clock is translated by the parabolic parameter;
* a formal parabolic shear clock composes additively.

Socketed:

* actual `dlog Q` generator in the smooth quadric-complement de Rham complex;
* Connes cocycle/Tomita--Takesaki realization;
* Bisognano--Wichmann/light-cone modular-flow identification;
* residue/monodromy period and Type III/KMS analytic realization.
-/

noncomputable section

namespace ModularTimeDeRhamBridge

open TKKJordanPairData.Legacy
open ChemicalPotentialDeRhamG0Bridge
open ThermodynamicTKKBridge
open ModularRadonNikodymJacobianBridge

/-- Formal parabolic shear clock.  Think of the unipotent matrix
`[[1, τ], [0, 1]]`; the finite kernel only needs the additive parameter. -/
structure ParabolicShearClock where
  τ : ℝ

/-- Composition of parabolic shear clocks adds their affine parameters. -/
def ParabolicShearClock.comp (A B : ParabolicShearClock) : ParabolicShearClock where
  τ := A.τ + B.τ

/-- Inverse clock reverses the affine parameter. -/
def ParabolicShearClock.inv (A : ParabolicShearClock) : ParabolicShearClock where
  τ := -A.τ

@[simp] theorem parabolic_shear_clock_add (A B : ParabolicShearClock) :
    (A.comp B).τ = A.τ + B.τ := rfl

@[simp] theorem parabolic_shear_clock_inv (A : ParabolicShearClock) :
    A.inv.τ = -A.τ := rfl

/-- Data asserting that the forbidden-cone `dlog Q` de Rham class is the same
object as the modular automorphism derivation, normalized by a KMS/residue
period.  The equality is intentionally socketed: it is the target of analytic
Tomita--Takesaki/de Rham comparison, not a hidden finite theorem. -/
structure DeRhamModularTimeIdentification
    (C : AbstractDeRhamComplex) (R : Type*) [CommRing R]
    (G : FiveGradedLieAlgebra R) where
  dlogForbiddenCone : DeRhamClass C 1
  modularDerivation : ModularDerivationG0 R G
  contractionClock : ℝ
  kmsResiduePeriod : ℝ
  deRhamGeneratorIsModularDerivation : Prop
  contraction_eq_kmsResiduePeriod : contractionClock = kmsResiduePeriod
  clocksParabolicTime : Prop
  residueMonodromyPeriod : Prop
  connesRovelliThermalTime : Prop
  bisognanoWichmannLightConeFlow : Prop

/-- The core finite consequence of the identification: the same derivation is a
`g₀` generator and preserves every TKK grade. -/
theorem dlog_modular_derivation_preserves_grades
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (C : AbstractDeRhamComplex)
    (I : DeRhamModularTimeIdentification C R G) :
    I.modularDerivation.derivationGenerator ∈ G.grade TKKGrade.z0 ∧
    (∀ i : TKKGrade, ∀ {x : G.L}, x ∈ G.grade i →
      ⁅I.modularDerivation.derivationGenerator, x⁆ ∈ G.grade i) := by
  exact ⟨I.modularDerivation.derivation_mem_g0,
    fun i x hx => modular_derivation_preserves_grade G I.modularDerivation i hx⟩

/-- Capstone finite/socket theorem: the forbidden-cone `dlog Q` class is
packaged as the modular derivation, the KMS/residue clock normalization is
recorded, and the parabolic/affine log-clock advances by the same parameter. -/
theorem modular_time_clocks_deRham_forbidden_cone
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    (C : AbstractDeRhamComplex)
    (I : DeRhamModularTimeIdentification C R G)
    (F : BogoliubovWeylChemicalPotential.BogoliubovInertialFrame)
    (a : AffineSimplexParameter)
    (P Q : ParabolicShearClock)
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
    nilpotentN * nilpotentN = 0 ∧
    (∀ t s : ℝ, parabolicTick t * parabolicTick s = parabolicTick (t + s)) ∧
    (∀ t : ℝ, parabolicTick t * parabolicTick (-t) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    BogoliubovWeylChemicalPotential.frameWeylLogClock
        { F with θ := F.θ + affineLogQ a } =
      BogoliubovWeylChemicalPotential.frameWeylLogClock F + affineLogQ a := by
  rcases dlog_modular_derivation_preserves_grades G C I with ⟨hg0, hpres⟩
  exact ⟨hg0, hpres, I.contraction_eq_kmsResiduePeriod, hId, hClock,
    hResidue, hThermal, hBW, parabolic_shear_clock_add P Q,
    nilpotentN_sq, parabolic_ticks_add, parabolic_tick_inverse,
    affine_rindler_translates_logClock F a⟩

end ModularTimeDeRhamBridge

end noncomputable section
