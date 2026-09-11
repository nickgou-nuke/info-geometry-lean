import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornG2SouriauTomitaBridge
import Mathlib.Tactic

/-!
# Finite G₂ Gibbs/Fisher to Souriau–Tomita bridge

This module closes the finite thermodynamic-to-operator edge for the canonical
rank-two Zorn Cartan lane.

For a finite Cartan Souriau datum, the Gibbs mean charge defines an operator-
valued Cartan moment canonically by scalar multiplication of the identity on the
native doubled Hilbert carrier.  The resulting Tomita modular Hamiltonian is
therefore the Massieu gradient pairing.  Independently, the curvature of the
same Massieu potential along the corresponding Cartan direction is exactly the
already-owned Fisher–Souriau quadratic form.

No density matrix, matrix-coordinate surrogate, or extra analytic hypothesis is
introduced.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2FiniteGibbsTomitaBridge

open scoped BigOperators

open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Lie.CanonicalZornG2SouriauTomitaBridge
open InfoGeometry.Canonical.SouriauTomitaModularFlowBridge
open InfoGeometry.Volume.ConnesCocycle
open InfoGeometry.Krein

abbrev G2Cartan := CanonicalZornRootSystemComparison.Cartan

variable {State : Type*} [Fintype State] [Nonempty State]
variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The rank-two thermodynamic direction selected by a canonical Cartan element. -/
def cartanThermalDirection (x : G2Cartan) : Fin 2 → ℝ :=
  fun i => simpleWeightOnCartan i x

/-- Gibbs expectation of the Cartan charge paired with a Cartan direction. -/
def finiteGibbsMeanPairing
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ)
    (x : G2Cartan) : ℝ :=
  ∑ i : Fin 2, cartanThermalDirection x i * souriauChargeMean D beta i

/-- The Gibbs mean pairing is the negative coordinate-gradient pairing of the Massieu potential. -/
theorem finiteGibbsMeanPairing_eq_neg_massieuGradient
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ)
    (x : G2Cartan) :
    finiteGibbsMeanPairing D beta x =
      -(∑ i : Fin 2,
        cartanThermalDirection x i *
          deriv (fun t => souriauMassieu D (betaSlice beta i t)) (beta i)) := by
  unfold finiteGibbsMeanPairing
  have hmean : ∀ i : Fin 2,
      souriauChargeMean D beta i =
        -deriv (fun t => souriauMassieu D (betaSlice beta i t)) (beta i) := by
    intro i
    have h := souriauMassieu_gradient_eq_neg_meanCharge D beta i
    linarith
  simp_rw [hmean]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  ring

/--
Canonical operator-valued Cartan moment obtained from the same finite Gibbs
ensemble: the thermodynamic mean charge acts as a scalar generator on the
native doubled Hilbert carrier.
-/
noncomputable def finiteGibbsMeanMomentOperator
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ)
    (x : G2Cartan) : AlgebraEnd H :=
  finiteGibbsMeanPairing D beta x •
    ContinuousLinearMap.id ℝ (DoubledSpace H)

/-- Canonical Cartan moment representation induced by the finite Gibbs mean map. -/
noncomputable def finiteGibbsCartanMomentRepresentation
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ) : CartanMomentRepresentation H where
  momentOperator := finiteGibbsMeanMomentOperator D beta

@[simp]
theorem finiteGibbsCartanMomentRepresentation_apply
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ)
    (x : G2Cartan) :
    (finiteGibbsCartanMomentRepresentation (H := H) D beta).momentOperator x =
      finiteGibbsMeanPairing D beta x •
        ContinuousLinearMap.id ℝ (DoubledSpace H) := by
  rfl

/-- The Tomita modular Hamiltonian is exactly the finite Gibbs mean Cartan generator. -/
theorem finiteGibbsTomita_modularHamiltonian_eq_meanPairing
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ)
    (x : G2Cartan) :
    (toSouriauTomitaLogContext
      (finiteGibbsCartanMomentRepresentation (H := H) D beta) x).modularHamiltonian =
      finiteGibbsMeanPairing D beta x •
        ContinuousLinearMap.id ℝ (DoubledSpace H) := by
  rw [toSouriauTomitaLogContext_modularHamiltonian]
  rfl

/--
Exact Massieu-gradient form of the finite Gibbs/Tomita modular Hamiltonian.
This is the theorem-level bridge from the finite exponential family to the
operatorial modular generator.
-/
theorem finiteGibbsTomita_modularHamiltonian_eq_neg_massieuGradient
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ)
    (x : G2Cartan) :
    (toSouriauTomitaLogContext
      (finiteGibbsCartanMomentRepresentation (H := H) D beta) x).modularHamiltonian =
      (-(∑ i : Fin 2,
        cartanThermalDirection x i *
          deriv (fun t => souriauMassieu D (betaSlice beta i t)) (beta i))) •
        ContinuousLinearMap.id ℝ (DoubledSpace H) := by
  rw [finiteGibbsTomita_modularHamiltonian_eq_meanPairing]
  rw [finiteGibbsMeanPairing_eq_neg_massieuGradient]

/--
The Massieu curvature in the Cartan direction used by the modular generator is
exactly the finite Fisher–Souriau quadratic form.
-/
theorem finiteGibbsTomita_massieuCurvature_eq_fisherSouriau
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ)
    (x : G2Cartan) :
    deriv (fun t => deriv
      (fun t' => souriauMassieu D
        (betaLine beta (cartanThermalDirection x) t')) t) 0 =
      fisherSouriauQuadratic D beta (cartanThermalDirection x) := by
  exact souriauMassieu_directionalSecondDeriv_eq_fisherSouriauQuadratic
    D beta (cartanThermalDirection x)

/-- The modular Cartan direction has nonnegative Fisher–Souriau curvature. -/
theorem finiteGibbsTomita_fisherSouriau_nonneg
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ)
    (x : G2Cartan) :
    0 ≤ fisherSouriauQuadratic D beta (cartanThermalDirection x) := by
  exact fisherSouriauQuadratic_nonneg D beta (cartanThermalDirection x)

/--
Complete finite Gibbs/Fisher–Tomita compatibility theorem for one Cartan
thermal direction.
-/
theorem finiteGibbsTomitaFisher_compatibility
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ)
    (x : G2Cartan) :
    (toSouriauTomitaLogContext
      (finiteGibbsCartanMomentRepresentation (H := H) D beta) x).modularHamiltonian =
        (-(∑ i : Fin 2,
          cartanThermalDirection x i *
            deriv (fun t => souriauMassieu D (betaSlice beta i t)) (beta i))) •
          ContinuousLinearMap.id ℝ (DoubledSpace H) ∧
    deriv (fun t => deriv
      (fun t' => souriauMassieu D
        (betaLine beta (cartanThermalDirection x) t')) t) 0 =
        fisherSouriauQuadratic D beta (cartanThermalDirection x) ∧
    0 ≤ fisherSouriauQuadratic D beta (cartanThermalDirection x) := by
  exact ⟨
    finiteGibbsTomita_modularHamiltonian_eq_neg_massieuGradient
      (H := H) D beta x,
    finiteGibbsTomita_massieuCurvature_eq_fisherSouriau D beta x,
    finiteGibbsTomita_fisherSouriau_nonneg D beta x⟩

end InfoGeometry.Lie.CanonicalZornG2FiniteGibbsTomitaBridge

end noncomputable section
