import Mathlib.Tactic.Ring
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornRootSystemComparison

/-!
# Rank-two Cartan Mellin characters

This file supplies the finite transform edge between the canonical rank-two
Cartan coordinates and multiplicative characters.  The character is written
in logarithmic Cartan coordinates, so its additive parameter law is proved
without introducing an analytic Mellin integral or a Weyl-group action.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 100000

open scoped BigOperators

namespace InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge

open InfoGeometry.Lie.CanonicalZornRootSystemComparison
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

/-- A rank-two Mellin character in logarithmic Cartan coordinates. -/
def rankTwoCartanMellinCharacter
    (s : Fin 2 → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  Complex.exp (-∑ i : Fin 2, s i * (t i : ℂ))

@[simp] theorem rankTwoCartanMellinCharacter_zero (s : Fin 2 → ℂ) :
    rankTwoCartanMellinCharacter s 0 = 1 := by
  simp [rankTwoCartanMellinCharacter]

theorem rankTwoCartanMellinCharacter_add
    (s : Fin 2 → ℂ) (t u : Fin 2 → ℝ) :
    rankTwoCartanMellinCharacter s (fun i => t i + u i) =
      rankTwoCartanMellinCharacter s t *
        rankTwoCartanMellinCharacter s u := by
  unfold rankTwoCartanMellinCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]
  ring

theorem rankTwoCartanMellinCharacter_ne_zero
    (s : Fin 2 → ℂ) (t : Fin 2 → ℝ) :
    rankTwoCartanMellinCharacter s t ≠ 0 := by
  unfold rankTwoCartanMellinCharacter
  exact Complex.exp_ne_zero _

theorem rankTwoCartanMellinCharacter_neg
    (s : Fin 2 → ℂ) (t : Fin 2 → ℝ) :
    rankTwoCartanMellinCharacter s (fun i => -t i) =
      (rankTwoCartanMellinCharacter s t)⁻¹ := by
  unfold rankTwoCartanMellinCharacter
  rw [← Complex.exp_neg]
  congr 1
  simp only [Pi.neg_apply, Complex.ofReal_neg, mul_neg, Finset.sum_neg_distrib,
    neg_neg]

abbrev Cartan := CanonicalZornRootSystemComparison.Cartan

/-- The rank-two Mellin character obtained from the canonical G₂ Cartan
simple-weight coordinates. -/
def canonicalG2CartanMellinCharacter
    (s : Fin 2 → ℂ) (x : Cartan) : ℂ :=
  rankTwoCartanMellinCharacter s
    (fun i => simpleWeightOnCartan i x)

theorem canonicalG2CartanMellinCharacter_add
    (s : Fin 2 → ℂ) (x y : Cartan) :
    canonicalG2CartanMellinCharacter s (x + y) =
      canonicalG2CartanMellinCharacter s x *
        canonicalG2CartanMellinCharacter s y := by
  unfold canonicalG2CartanMellinCharacter
  have hweights :
      (fun i => simpleWeightOnCartan i (x + y)) =
        (fun i => simpleWeightOnCartan i x + simpleWeightOnCartan i y) := by
    funext i
    simp [simpleWeightOnCartan, map_add]
  rw [hweights]
  exact rankTwoCartanMellinCharacter_add s _ _

theorem canonicalG2CartanMellinCharacter_ne_zero
    (s : Fin 2 → ℂ) (x : Cartan) :
    canonicalG2CartanMellinCharacter s x ≠ 0 := by
  unfold canonicalG2CartanMellinCharacter
  exact rankTwoCartanMellinCharacter_ne_zero s _

theorem canonicalG2CartanMellinCharacter_neg
    (s : Fin 2 → ℂ) (x : Cartan) :
    canonicalG2CartanMellinCharacter s (-x) =
      (canonicalG2CartanMellinCharacter s x)⁻¹ := by
  unfold canonicalG2CartanMellinCharacter
  have hweights :
      (fun i => simpleWeightOnCartan i (-x)) =
        (fun i => -simpleWeightOnCartan i x) := by
    funext i
    simp [simpleWeightOnCartan, map_neg]
  rw [hweights, rankTwoCartanMellinCharacter_neg]

@[simp] theorem canonicalG2CartanMellinCharacter_zero
    (s : Fin 2 → ℂ) :
    canonicalG2CartanMellinCharacter s 0 = 1 := by
  simp [canonicalG2CartanMellinCharacter, rankTwoCartanMellinCharacter,
    simpleWeightOnCartan, CanonicalZornRootPairing.simpleWeight,
    CanonicalZornCartanAdjointRootDecomposition.coordWeight]

/-- The Mellin character promoted to a multiplicative unit `ℂˣ`. -/
def canonicalG2CartanMellinCharacterUnits
    (s : Fin 2 → ℂ) (x : Cartan) : ℂˣ :=
  Units.mk0 (canonicalG2CartanMellinCharacter s x)
    (canonicalG2CartanMellinCharacter_ne_zero s x)

/-- The API consolidation: Mellin character as a canonical homomorphism
from `(Cartan, +)` to `(ℂˣ, ×)`. -/
def canonicalG2CartanMellinCharacterHom (s : Fin 2 → ℂ) :
    Multiplicative Cartan →* ℂˣ where
  toFun x := canonicalG2CartanMellinCharacterUnits s (Multiplicative.toAdd x)
  map_one' := by
    ext
    exact canonicalG2CartanMellinCharacter_zero s
  map_mul' x y := by
    ext
    exact canonicalG2CartanMellinCharacter_add s (Multiplicative.toAdd x) (Multiplicative.toAdd y)

end InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
