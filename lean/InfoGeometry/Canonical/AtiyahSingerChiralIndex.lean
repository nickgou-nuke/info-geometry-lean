import InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace

/-!
# Chiral Dirac operators in a noncommutative algebra

This owner formalizes the algebraic parity and cyclic-trace cancellation for
an odd Dirac operator over an arbitrary associative operator ring. The trace
range is required to have no 2-torsion for the odd-square cancellation. This
does not construct a Fredholm index or prove the Atiyah--Singer theorem.
-/

namespace AtiyahSingerIndex

open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace

structure ChiralDiracOperator (A : Type*) [Ring A] where
  D_val : A
  gamma5 : A
  h_gamma5_sq : gamma5 * gamma5 = 1
  h_chiral_anti : gamma5 * D_val + D_val * gamma5 = 0

namespace ChiralDiracOperator

variable {A : Type*} [Ring A] (chiral : ChiralDiracOperator A)

/-- The grading stored in the Dirac package is involutive. -/
theorem gamma5_involution : chiral.gamma5 * chiral.gamma5 = 1 :=
  chiral.h_gamma5_sq

/-- The Dirac operator is odd under its chiral grading. -/
theorem chiral_anti_commute :
    chiral.gamma5 * chiral.D_val = -(chiral.D_val * chiral.gamma5) :=
  eq_neg_of_add_eq_zero_left chiral.h_chiral_anti

/-- Conjugation by the involutive grading reverses the odd Dirac operator. -/
theorem grading_conjugates_Dirac_to_neg :
    chiral.gamma5 * chiral.D_val * chiral.gamma5 = -chiral.D_val := by
  calc
    chiral.gamma5 * chiral.D_val * chiral.gamma5 =
        -(chiral.D_val * chiral.gamma5) * chiral.gamma5 := by
      rw [chiral.chiral_anti_commute]
    _ = -(chiral.D_val * (chiral.gamma5 * chiral.gamma5)) := by
      simp only [neg_mul, mul_assoc]
    _ = -chiral.D_val := by rw [chiral.gamma5_involution, mul_one]

/-- The square of an odd Dirac operator is an even operator: it commutes
with the grading in the noncommutative operator algebra. -/
theorem dirac_square_commutes_with_grading :
    chiral.gamma5 * (chiral.D_val * chiral.D_val) =
      (chiral.D_val * chiral.D_val) * chiral.gamma5 := by
  calc
    chiral.gamma5 * (chiral.D_val * chiral.D_val) =
        (chiral.gamma5 * chiral.D_val) * chiral.D_val := by rw [mul_assoc]
    _ = -(chiral.D_val * chiral.gamma5) * chiral.D_val := by
      rw [chiral.chiral_anti_commute]
    _ = -(chiral.D_val * (chiral.gamma5 * chiral.D_val)) := by
      simp only [neg_mul, mul_assoc]
    _ = -(chiral.D_val * (-(chiral.D_val * chiral.gamma5))) := by
      rw [chiral.chiral_anti_commute]
    _ = (chiral.D_val * chiral.D_val) * chiral.gamma5 := by
      simp only [mul_neg, neg_neg, mul_assoc]

/-- Algebraic graded trace of the Dirac square for a supplied cyclic
functional. -/
def mckeanSingerIndex {R : Type*} [AddCommGroup R]
    (τ : A →+ R) : R :=
  gradedTrace τ chiral.gamma5 (chiral.D_val * chiral.D_val)

/-- The odd Dirac square has zero cyclic graded trace when the range is
2-torsion-free. This is a finite algebraic cancellation identity, not a heat
kernel or Fredholm-index theorem. -/
theorem mckean_singer_index_zero {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclic τ)
    (h_two_torsion_free : ∀ r : R, r + r = 0 → r = 0) :
    chiral.mckeanSingerIndex τ = 0 := by
  exact gradedTrace_odd_square_eq_zero τ hτ h_two_torsion_free
    chiral.h_chiral_anti

end ChiralDiracOperator

end AtiyahSingerIndex
