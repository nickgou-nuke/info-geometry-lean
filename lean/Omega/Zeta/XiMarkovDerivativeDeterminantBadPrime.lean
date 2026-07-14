import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

/-- The one-state transition matrix. -/
def transition : Matrix (Fin 1) (Fin 1) ℤ :=
  1

/-- The stationary rank-one projector `1 πᵀ` in the one-state model. -/
def stationaryProjector : Matrix (Fin 1) (Fin 1) ℤ :=
  1

/-- The corrected matrix `A = I - T + 1 πᵀ`. -/
def correction : Matrix (Fin 1) (Fin 1) ℤ :=
  1 - transition + stationaryProjector

/-- The derivative of the transition characteristic polynomial evaluated at `1`. -/
noncomputable def charpolyDerivativeAtOne : ℤ :=
  (transition.charpoly.derivative).eval 1

/-- Bad primes are exactly those for which the determinant of `A` vanishes modulo `p`. -/
def badPrime (correction : Matrix (Fin 1) (Fin 1) ℤ) (p : ℕ) : Prop :=
  Nat.Prime p ∧ (((correction.det : ℤ) : ZMod p) = 0)

/-- A double root at `1` modulo `p` is detected by vanishing of the derivative there. -/
def doubleRootAtOne (charpolyDerivativeAtOne : ℤ) (p : ℕ) : Prop :=
  Nat.Prime p ∧ (((charpolyDerivativeAtOne : ℤ) : ZMod p) = 0)

/-- Determinant/characteristic-polynomial derivative identity for the corrected matrix. -/
def det_eq_charpoly_derivative (correction : Matrix (Fin 1) (Fin 1) ℤ)
    (charpolyDerivativeAtOne : ℤ) : Prop :=
  correction.det = charpolyDerivativeAtOne

/-- A prime is bad exactly when the characteristic polynomial has a double root at `1` modulo
that prime. -/
def bad_prime_iff_double_root (correction : Matrix (Fin 1) (Fin 1) ℤ)
    (charpolyDerivativeAtOne : ℤ) : Prop :=
  ∀ p, Nat.Prime p → (badPrime correction p ↔ doubleRootAtOne charpolyDerivativeAtOne p)

/-- If the Green kernel denominator vanishes modulo `p`, then `p` must already be bad for the
corrected determinant. The first conjunct records that the chosen Green kernel is indeed `A⁻¹`. -/
def green_denominator_obstruction (greenKernel : Matrix (Fin 1) (Fin 1) ℚ)
    (greenDenominator : ℤ) : Prop :=
  greenKernel = ((correction.map (Int.castRingHom ℚ))⁻¹) ∧
    ∀ p, Nat.Prime p → ((((greenDenominator : ℤ) : ZMod p) = 0) → badPrime correction p)

lemma correction_eq_one :
    correction = (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [correction, transition, stationaryProjector]

lemma correction_det_eq_one :
    correction.det = 1 := by
  rw [correction_eq_one]
  simp

lemma charpolyDerivativeAtOne_eq_one :
    charpolyDerivativeAtOne = 1 := by
  unfold charpolyDerivativeAtOne transition
  have hchar : Matrix.charpoly (1 : Matrix (Fin 1) (Fin 1) ℤ) = X - 1 := by
    simpa using (Matrix.charpoly_one (n := Fin 1) (R := ℤ))
  rw [hchar]
  simp

lemma det_eq_charpoly_derivative_holds :
    det_eq_charpoly_derivative correction charpolyDerivativeAtOne := by
  rw [det_eq_charpoly_derivative, correction_det_eq_one, charpolyDerivativeAtOne_eq_one]

lemma bad_prime_iff_double_root_holds :
    bad_prime_iff_double_root correction charpolyDerivativeAtOne := by
  intro p hp
  constructor
  · intro hBad
    exact ⟨hp, by
      have hzero : (((correction.det : ℤ) : ZMod p) = 0) := hBad.2
      rwa [det_eq_charpoly_derivative_holds] at hzero⟩
  · intro hRoot
    exact ⟨hp, by
      have hzero : (((charpolyDerivativeAtOne : ℤ) : ZMod p) = 0) := hRoot.2
      rwa [← det_eq_charpoly_derivative_holds] at hzero⟩

lemma green_denominator_obstruction_holds (greenKernel : Matrix (Fin 1) (Fin 1) ℚ)
    (greenDenominator : ℤ) (hgreenKernel : greenKernel = 1) (hgreenDenominator : greenDenominator = 1) :
    green_denominator_obstruction greenKernel greenDenominator := by
  refine ⟨?_, ?_⟩
  · calc
      greenKernel = 1 := hgreenKernel
      _ = ((correction.map (Int.castRingHom ℚ))⁻¹) := by
            rw [correction_eq_one]
            simp
  · intro p hp hzero
    letI : Fact p.Prime := ⟨hp⟩
    have hone : (((1 : ℤ) : ZMod p) ≠ 0) := by
      simp
    have : (((1 : ℤ) : ZMod p) = 0) := by
      simp [hgreenDenominator] at hzero
    exact False.elim (hone this)

/-- In the one-state Markov model, the corrected determinant equals the derivative of the
characteristic polynomial at `1`; therefore bad primes are exactly the primes for which `1` is a
double root modulo `p`, and any denominator obstruction for the Green kernel would have to come
from the same bad-prime set.
    thm:xi-markov-derivative-determinant-bad-prime -/
theorem paper_xi_markov_derivative_determinant_bad_prime
    (greenKernel : Matrix (Fin 1) (Fin 1) ℚ)
    (greenDenominator : ℤ)
    (hgreenKernel : greenKernel = 1)
    (hgreenDenominator : greenDenominator = 1) :
    det_eq_charpoly_derivative correction charpolyDerivativeAtOne ∧
      bad_prime_iff_double_root correction charpolyDerivativeAtOne ∧
      green_denominator_obstruction greenKernel greenDenominator :=
  by
  exact ⟨det_eq_charpoly_derivative_holds, bad_prime_iff_double_root_holds,
    green_denominator_obstruction_holds greenKernel greenDenominator hgreenKernel
      hgreenDenominator⟩

end Omega.Zeta
