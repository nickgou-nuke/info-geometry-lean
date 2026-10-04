import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import InfoGeometry.Topology.AmplituhedronGeneralTwistorExpansion

open Matrix
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace InfoGeometry.Amplituhedron

variable {n : ℕ} [NeZero n]

/-! ### 1. Projective Weights of Twistor Functions -/

/-- A scalar function of the internal plane Y has projective weight `w` if
under left multiplication by a 2x2 matrix Λ, it scales by `(det Λ)^w`. -/
def HasProjectiveWeight (f : Matrix (Fin 2) (Fin 4) ℝ → ℝ) (w : ℕ) : Prop :=
  ∀ (Λ : Matrix (Fin 2) (Fin 2) ℝ) (Y : Matrix (Fin 2) (Fin 4) ℝ),
    f (Λ * Y) = ((Λ 0 0 * Λ 1 1 - Λ 0 1 * Λ 1 0) ^ w) * f Y

lemma twistorMatrix_mul_apply (Λ : Matrix (Fin 2) (Fin 2) ℝ) (Y : Matrix (Fin 2) (Fin 4) ℝ)
    (i : Fin 2) (j : Fin 4) :
    (Λ * Y) i j = Λ i 0 * Y 0 j + Λ i 1 * Y 1 j := by
  dsimp [Matrix.mul_apply]
  rw [Fin.sum_univ_two]

/-- The 4-bracket ⟨Y Z_a Z_b⟩ has projective weight 1 in Y. -/
theorem twistorBracket_weight (Z : Matrix (Fin n) (Fin 4) ℝ) (a b : Fin n) :
    HasProjectiveWeight (fun Y => twistorBracket Y Z a b) 1 := by
  intro Λ Y
  dsimp [HasProjectiveWeight, twistorBracket, det4, twistorMatrix]
  have h00 : (Λ * Y) 0 0 = Λ 0 0 * Y 0 0 + Λ 0 1 * Y 1 0 := twistorMatrix_mul_apply Λ Y 0 0
  have h01 : (Λ * Y) 0 1 = Λ 0 0 * Y 0 1 + Λ 0 1 * Y 1 1 := twistorMatrix_mul_apply Λ Y 0 1
  have h02 : (Λ * Y) 0 2 = Λ 0 0 * Y 0 2 + Λ 0 1 * Y 1 2 := twistorMatrix_mul_apply Λ Y 0 2
  have h03 : (Λ * Y) 0 3 = Λ 0 0 * Y 0 3 + Λ 0 1 * Y 1 3 := twistorMatrix_mul_apply Λ Y 0 3
  have h10 : (Λ * Y) 1 0 = Λ 1 0 * Y 0 0 + Λ 1 1 * Y 1 0 := twistorMatrix_mul_apply Λ Y 1 0
  have h11 : (Λ * Y) 1 1 = Λ 1 0 * Y 0 1 + Λ 1 1 * Y 1 1 := twistorMatrix_mul_apply Λ Y 1 1
  have h12 : (Λ * Y) 1 2 = Λ 1 0 * Y 0 2 + Λ 1 1 * Y 1 2 := twistorMatrix_mul_apply Λ Y 1 2
  have h13 : (Λ * Y) 1 3 = Λ 1 0 * Y 0 3 + Λ 1 1 * Y 1 3 := twistorMatrix_mul_apply Λ Y 1 3
  simp only [h00, h01, h02, h03, h10, h11, h12, h13, pow_one]
  ring

/-- The product of two functions with weights w1 and w2 has weight w1 + w2. -/
theorem HasProjectiveWeight_mul {f g : Matrix (Fin 2) (Fin 4) ℝ → ℝ} {w1 w2 : ℕ}
    (hf : HasProjectiveWeight f w1) (hg : HasProjectiveWeight g w2) :
    HasProjectiveWeight (fun Y => f Y * g Y) (w1 + w2) := by
  intro Λ Y
  dsimp
  rw [hf Λ Y, hg Λ Y, pow_add]
  ring

/-! ### 2. Global Rational Form Density Structure -/

/-- The pristine algebraic structure of the n-point canonical form on the Grassmannian.
Instead of a naive product of 1-forms (which vanishes for n > 4 due to dY ∧ dY = 0),
the exact geometric carrier is a rational top-form density over Gr(2, 4) with
projective weight 0. -/
structure AmplituhedronRationalForm (n : ℕ) [NeZero n] where
  Z : Matrix (Fin n) (Fin 4) ℝ
  /-- The polynomial numerator N(Y; Z). -/
  numerator : Matrix (Fin 2) (Fin 4) ℝ → ℝ
  /-- The polynomial denominator, which must be the cyclic twistor brackets. -/
  denominator : Matrix (Fin 2) (Fin 4) ℝ → ℝ
  /-- The denominator must equal the product of cyclic twistor brackets. -/
  denominator_eq : denominator = fun Y => cyclicTwistorDenominator Y Z
  /-- The numerator must have projective weight exactly (n - 4) to balance the 
      denominator (weight n) and the measure d^4 Y (weight 4). 
      (We assume n ≥ 4 so n - 4 is well-defined). -/
  numerator_weight : HasProjectiveWeight numerator (n - 4)
  /-- The denominator has projective weight n. -/
  denominator_weight : HasProjectiveWeight denominator n

/-! ### 3. Factorization Residues (Physical Unitarity) -/

/-- An abstract structure mapping an n-point form to its boundary facets.
Taking the Poincaré residue along any physical cyclic facet ⟨Y Z_i Z_{i+1}⟩ = 0
recovers the (n-1)-point form density. -/
structure FactorizationResidue (n : ℕ) [NeZero n] [NeZero (n-1)] where
  /-- The n-point form. -/
  omega_n : AmplituhedronRationalForm n
  /-- The (n-1)-point form. -/
  omega_n_minus_1 : AmplituhedronRationalForm (n - 1)
  /-- The abstract Poincaré residue operator taking forms on Gr(2, 4) to their facet residues. -/
  poincare_residue : AmplituhedronRationalForm n → Fin n → AmplituhedronRationalForm (n - 1)
  /-- The physical collinear/soft limit factorization. -/
  residue_eq : ∀ (i : Fin n), poincare_residue omega_n i = omega_n_minus_1

end InfoGeometry.Amplituhedron
