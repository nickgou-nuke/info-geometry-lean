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

/-! ### 2. Homogeneity of the cyclic denominator

The bracket product has projective weight `n`.  This is a property of the
explicit algebraic denominator, and does not by itself construct a canonical
form or a Poincaré residue. -/

theorem cyclicTwistorDenominator_weight (Z : Matrix (Fin n) (Fin 4) ℝ) :
    HasProjectiveWeight (fun Y => cyclicTwistorDenominator Y Z) n := by
  intro Λ Y
  let detΛ : ℝ := Λ 0 0 * Λ 1 1 - Λ 0 1 * Λ 1 0
  have hbr (i : Fin n) :
      twistorBracket (Λ * Y) Z i (cyclicNext i) =
        detΛ * twistorBracket Y Z i (cyclicNext i) := by
    exact (twistorBracket_weight Z i (cyclicNext i) Λ Y).trans
      (by simp [HasProjectiveWeight, detΛ, pow_one])
  change (∏ i : Fin n, twistorBracket (Λ * Y) Z i (cyclicNext i)) =
      detΛ ^ n * ∏ i : Fin n, twistorBracket Y Z i (cyclicNext i)
  calc
    _ = ∏ i : Fin n, detΛ * twistorBracket Y Z i (cyclicNext i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hbr i
    _ = (∏ _i : Fin n, detΛ) *
        ∏ i : Fin n, twistorBracket Y Z i (cyclicNext i) := by
      rw [Finset.prod_mul_distrib]
    _ = detΛ ^ n *
        ∏ i : Fin n, twistorBracket Y Z i (cyclicNext i) := by
      simp [detΛ]

/-! ### Development frontier

A genuine canonical form requires specifying the positive cell, its rational
numerator, and the differential form or density transformation law.  Boundary
factorization further requires a defined residue operation and a theorem about
that operation.  Those data are not consequences of denominator homogeneity,
so this module leaves both constructions open. -/

end InfoGeometry.Amplituhedron
