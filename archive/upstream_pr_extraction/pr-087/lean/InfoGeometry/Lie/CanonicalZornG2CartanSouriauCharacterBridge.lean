import InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
import InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
import InfoGeometry.Physics.SouriauMassieuPlanckFunctional

/-!
# Finite Souriau reading of the native Cartan character

This owner supplies the missing finite datum only: a state space, a rank-two
Cartan charge (a finite moment-map readout), and a generalized inverse
temperature.  Its unnormalized Gibbs kernel is exactly the existing Cartan
Mellin character.  No symplectic manifold or analytic integral is asserted.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge

open InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
open InfoGeometry.Lie.CanonicalZornG2CartanMellinWeylBridge
open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Physics.SouriauMassieuPlanckFunctional

abbrev G2Cartan := CanonicalZornRootSystemComparison.Cartan

structure CartanSouriauDatum (State : Type*) where
  momentMap : State → Fin 2 → ℝ
  beta : Fin 2 → ℂ

def pairingEnergy {State : Type*}
    (D : CartanSouriauDatum State) (x : State) : ℂ :=
  ∑ i : Fin 2, D.beta i * (D.momentMap x i : ℂ)

def unnormalizedGibbsKernel {State : Type*}
    (D : CartanSouriauDatum State) (x : State) : ℂ :=
  Complex.exp (-(pairingEnergy D x))

theorem unnormalizedGibbsKernel_eq_cartanCharacter {State : Type*}
    (D : CartanSouriauDatum State) (x : State) :
    unnormalizedGibbsKernel D x =
      rankTwoCartanMellinCharacter D.beta (D.momentMap x) := rfl

def canonicalCartanSouriauDatum : CartanSouriauDatum G2Cartan where
  momentMap x i := simpleWeightOnCartan i x
  beta := fun i => Complex.I * (1 : ℂ)

theorem canonicalCartanKernel_eq_canonicalG2Character (x : G2Cartan) :
    unnormalizedGibbsKernel canonicalCartanSouriauDatum x =
      canonicalG2CartanMellinCharacter
        (fun _ => Complex.I) x := by
  simp [unnormalizedGibbsKernel, pairingEnergy,
    canonicalCartanSouriauDatum, canonicalG2CartanMellinCharacter,
    rankTwoCartanMellinCharacter]

def realPairingEnergy {State : Type*}
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ) (x : State) : ℝ :=
  ∑ i : Fin 2, beta i * D.momentMap x i

def realGibbsKernel {State : Type*}
    (D : CartanSouriauDatum State)
    (beta : Fin 2 → ℝ) (x : State) : ℝ :=
  Real.exp (-(realPairingEnergy D beta x))

def realGibbsPartition {State : Type*} [Fintype State]
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) : ℝ :=
  ∑ x : State, realGibbsKernel D beta x

theorem realGibbsPartition_pos {State : Type*} [Fintype State] [Nonempty State]
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) :
    0 < realGibbsPartition D beta := by
  unfold realGibbsPartition
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

def realGibbsWeight {State : Type*} [Fintype State]
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) (x : State) : ℝ :=
  realGibbsKernel D beta x / realGibbsPartition D beta

theorem realGibbsWeight_sum_eq_one {State : Type*}
    [Fintype State] [Nonempty State]
    (D : CartanSouriauDatum State) (beta : Fin 2 → ℝ) :
    (∑ x : State, realGibbsWeight D beta x) = 1 := by
  unfold realGibbsWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (realGibbsPartition_pos D beta))

/-- Spectral/Thermodynamic covariance under the short Weyl reflection. -/
theorem canonicalCartanKernel_short_covariant (beta : Fin 2 → ℂ) (x : G2Cartan) :
    unnormalizedGibbsKernel { canonicalCartanSouriauDatum with beta := beta } (canonicalShortReflection x) =
      unnormalizedGibbsKernel { canonicalCartanSouriauDatum with beta := canonicalShortReflectionDual beta } x := by
  rw [unnormalizedGibbsKernel_eq_cartanCharacter]
  rw [unnormalizedGibbsKernel_eq_cartanCharacter]
  change canonicalG2CartanMellinCharacter beta (canonicalShortReflection x) =
    canonicalG2CartanMellinCharacter (canonicalShortReflectionDual beta) x
  exact canonicalG2CartanMellinCharacter_short_covariant beta x

/-- Spectral/Thermodynamic covariance under the long Weyl reflection. -/
theorem canonicalCartanKernel_long_covariant (beta : Fin 2 → ℂ) (x : G2Cartan) :
    unnormalizedGibbsKernel { canonicalCartanSouriauDatum with beta := beta } (canonicalLongReflection x) =
      unnormalizedGibbsKernel { canonicalCartanSouriauDatum with beta := canonicalLongReflectionDual beta } x := by
  rw [unnormalizedGibbsKernel_eq_cartanCharacter]
  rw [unnormalizedGibbsKernel_eq_cartanCharacter]
  change canonicalG2CartanMellinCharacter beta (canonicalLongReflection x) =
    canonicalG2CartanMellinCharacter (canonicalLongReflectionDual beta) x
  exact canonicalG2CartanMellinCharacter_long_covariant beta x

end InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
