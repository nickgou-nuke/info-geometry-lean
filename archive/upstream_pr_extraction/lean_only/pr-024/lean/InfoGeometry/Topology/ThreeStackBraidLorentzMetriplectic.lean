import Mathlib

/-!
# Finite three-stack braid--Lorentz--metriplectic packet

This file mirrors `tools/sympy/three_stack_braid_lorentz_metriplectic.py`.

It proves only finite algebraic facts:
* a rational `1+1` boost preserves the diagonal form `diag(-1,1)`;
* central signs `{+I,-I}` are fixed by conjugation with that boost;
* adjacent transpositions on four letters satisfy adjacent/distant braid relations;
* the finite metriplectic atom `Jᵀ=-J`, `J²=-I`, `Gᵀ=G`.

It does **not** prove `SO⁺(1,3)`, a faithful `B₄ → Aut(F₄)` theorem, Mac Lane
hexagon coherence, anomaly-free TQFT, a mass gap, super-Kähler geometry, or
metriplectic thermodynamics.
-/

namespace InfoGeometry.Topology.ThreeStackBraidLorentzMetriplectic

abbrev Mat2Q := Matrix (Fin 2) (Fin 2) ℚ

/-- The `1+1` Minkowski metric with signature `(-,+)`. -/
def eta : Mat2Q :=
  ![![-1, 0], ![0, 1]]

/-- A rational Lorentz boost: `(5/4)^2 - (3/4)^2 = 1`. -/
def boost : Mat2Q :=
  ![![5 / 4, 3 / 4], ![3 / 4, 5 / 4]]

/-- Explicit inverse of `boost`. -/
def boostInv : Mat2Q :=
  ![![5 / 4, -3 / 4], ![-3 / 4, 5 / 4]]

/-- Finite symplectic/complex atom for the conservative channel. -/
def J : Mat2Q :=
  ![![0, 1], ![-1, 0]]

/-- Finite metric atom for the dissipative channel. -/
def G : Mat2Q :=
  1

@[simp]
theorem boost_mul_inv : boost * boostInv = (1 : Mat2Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [boost, boostInv, Matrix.mul_apply]

@[simp]
theorem inv_mul_boost : boostInv * boost = (1 : Mat2Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [boost, boostInv, Matrix.mul_apply]

/-- The rational boost preserves the `1+1` Lorentz form. -/
theorem boost_preserves_eta : boost.transpose * eta * boost = eta := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [boost, eta, Matrix.mul_apply]

/-- Conjugation by the rational boost fixes `+I`. -/
theorem boost_conj_one : boost * (1 : Mat2Q) * boostInv = 1 := by
  simp

/-- Conjugation by the rational boost fixes `-I`. -/
theorem boost_conj_neg_one : boost * (-(1 : Mat2Q)) * boostInv = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [boost, boostInv, Matrix.mul_apply]

@[simp]
theorem J_skew : J.transpose = -J := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J]

@[simp]
theorem J_sq : J * J = -(1 : Mat2Q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J, Matrix.mul_apply]

@[simp]
theorem G_symmetric : G.transpose = G := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [G]

/-- Adjacent transposition `(12)` on four letters, zero-indexed. -/
def sigma1 : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 3

/-- Adjacent transposition `(23)` on four letters, zero-indexed. -/
def sigma2 : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 3

/-- Adjacent transposition `(34)` on four letters, zero-indexed. -/
def sigma3 : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

/-- Finite `S₄` shadow of the adjacent Artin relation. -/
theorem s4_adjacent_artin (x : Fin 4) :
    sigma1 (sigma2 (sigma1 x)) = sigma2 (sigma1 (sigma2 x)) := by
  fin_cases x <;> rfl

/-- Finite `S₄` shadow of distant braid-generator commutativity. -/
theorem s4_distant_commutes (x : Fin 4) :
    sigma1 (sigma3 x) = sigma3 (sigma1 x) := by
  fin_cases x <;> rfl

/-- Summary theorem for the finite, theorem-safe three-stack packet. -/
theorem finite_three_stack_packet :
    boost.transpose * eta * boost = eta ∧
      boost * (1 : Mat2Q) * boostInv = 1 ∧
      boost * (-(1 : Mat2Q)) * boostInv = -1 ∧
      J.transpose = -J ∧
      J * J = -(1 : Mat2Q) ∧
      G.transpose = G ∧
      (∀ x : Fin 4, sigma1 (sigma2 (sigma1 x)) = sigma2 (sigma1 (sigma2 x))) ∧
      (∀ x : Fin 4, sigma1 (sigma3 x) = sigma3 (sigma1 x)) := by
  exact ⟨boost_preserves_eta, boost_conj_one, boost_conj_neg_one, J_skew, J_sq,
    G_symmetric, s4_adjacent_artin, s4_distant_commutes⟩

end InfoGeometry.Topology.ThreeStackBraidLorentzMetriplectic
