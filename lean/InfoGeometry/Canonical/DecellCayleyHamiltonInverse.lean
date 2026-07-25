import Mathlib.Tactic

/-!
# Decell Cayley-Hamilton Inversion

Finite algebraic layer extracted from Henry P. Decell, Jr.,
"An Application of the Cayley-Hamilton Theorem to Generalized Matrix
Inversion" (SIAM Review 7, 1965, 526--528).

The paper uses Cayley-Hamilton on `A A*` to compute the Moore-Penrose inverse.
This file formalizes the theorem-safe coefficient-tail step over a field.  The
full rectangular Moore-Penrose equations are checked separately by exact
rational matrix computation in `tools/sympy/decell_cayley_hamilton_inverse.py`.

Degree-two and degree-three Cayley-Hamilton tail formulas give explicit
one-sided inverses when the final displayed coefficient is nonzero.  The
inverse conclusions depend on explicit polynomial equations and explicit
nonzero coefficient hypotheses.
-/

namespace InfoGeometry.Canonical.DecellCayleyHamiltonInverse

noncomputable section

variable {R : Type} [Field R]

/-- Decell's degree-two inverse candidate from `B^2 + a₁B + a₂ = 0`. -/
def decellInverseCandidateTwo (a₁ a₂ B : R) : R :=
  -(a₂)⁻¹ * (B + a₁)

/--
If `B` satisfies `B^2 + a₁B + a₂ = 0` and `a₂ ≠ 0`, Decell's tail is a
right inverse for `B`.
-/
theorem decell_inverse_candidate_two_right
    (a₁ a₂ B : R)
    (hpoly : B ^ 2 + a₁ * B + a₂ = 0)
    (ha₂ : a₂ ≠ 0) :
    B * decellInverseCandidateTwo a₁ a₂ B = 1 := by
  unfold decellInverseCandidateTwo
  have htail : B ^ 2 + a₁ * B = -a₂ := by
    rw [← sub_eq_zero]
    linear_combination hpoly
  calc
    B * (-(a₂)⁻¹ * (B + a₁)) = -(a₂)⁻¹ * (B ^ 2 + a₁ * B) := by ring
    _ = -(a₂)⁻¹ * (-a₂) := by rw [htail]
    _ = 1 := by field_simp [ha₂]

/--
In a commutative field, the same degree-two candidate is also a left inverse.
-/
theorem decell_inverse_candidate_two_left
    (a₁ a₂ B : R)
    (hpoly : B ^ 2 + a₁ * B + a₂ = 0)
    (ha₂ : a₂ ≠ 0) :
    decellInverseCandidateTwo a₁ a₂ B * B = 1 := by
  rw [mul_comm]
  exact decell_inverse_candidate_two_right a₁ a₂ B hpoly ha₂

/-- Decell's degree-three inverse candidate from `B^3 + a₁B^2 + a₂B + a₃ = 0`. -/
def decellInverseCandidateThree (a₁ a₂ a₃ B : R) : R :=
  -(a₃)⁻¹ * (B ^ 2 + a₁ * B + a₂)

/--
If `B` satisfies `B^3 + a₁B^2 + a₂B + a₃ = 0` and `a₃ ≠ 0`, Decell's tail
is a right inverse for `B`.
-/
theorem decell_inverse_candidate_three_right
    (a₁ a₂ a₃ B : R)
    (hpoly : B ^ 3 + a₁ * B ^ 2 + a₂ * B + a₃ = 0)
    (ha₃ : a₃ ≠ 0) :
    B * decellInverseCandidateThree a₁ a₂ a₃ B = 1 := by
  unfold decellInverseCandidateThree
  have htail : B ^ 3 + a₁ * B ^ 2 + a₂ * B = -a₃ := by
    rw [← sub_eq_zero]
    linear_combination hpoly
  calc
    B * (-(a₃)⁻¹ * (B ^ 2 + a₁ * B + a₂))
        = -(a₃)⁻¹ * (B ^ 3 + a₁ * B ^ 2 + a₂ * B) := by ring
    _ = -(a₃)⁻¹ * (-a₃) := by rw [htail]
    _ = 1 := by field_simp [ha₃]

/--
In a commutative field, the same degree-three candidate is also a left inverse.
-/
theorem decell_inverse_candidate_three_left
    (a₁ a₂ a₃ B : R)
    (hpoly : B ^ 3 + a₁ * B ^ 2 + a₂ * B + a₃ = 0)
    (ha₃ : a₃ ≠ 0) :
    decellInverseCandidateThree a₁ a₂ a₃ B * B = 1 := by
  rw [mul_comm]
  exact decell_inverse_candidate_three_right a₁ a₂ a₃ B hpoly ha₃

end

end InfoGeometry.Canonical.DecellCayleyHamiltonInverse
