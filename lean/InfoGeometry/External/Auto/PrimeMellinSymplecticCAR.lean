import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix
open scoped BigOperators

noncomputable section

namespace PrimeMellinSymplecticCAR

variable {n : ℕ}

/-- Prime-Mellin Vandermonde matrix with nodes `p_i^{-1}`. -/
noncomputable def primeMellinVandermonde (p : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  vandermonde fun i => (p i : ℝ)⁻¹

lemma primeMellin_nodes_injective (p : Fin n → ℕ) (hp : Function.Injective p) :
    Function.Injective (fun i => (p i : ℝ)⁻¹) := by
  intro i j hij
  have hq : (p i : ℝ) = (p j : ℝ) := by
    exact inv_inj.mp hij
  exact hp (by exact_mod_cast hq)

/-- The prime-Mellin Vandermonde matrix is invertible whenever the prime indexing is injective. -/
theorem det_primeMellinVandermonde_ne_zero
    (p : Fin n → ℕ) (hp : Function.Injective p) :
    det (primeMellinVandermonde p) ≠ 0 := by
  rw [primeMellinVandermonde, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i hi
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hlt : i < j := Finset.mem_Ioi.mp hj
  have hneq : (p j : ℝ)⁻¹ ≠ (p i : ℝ)⁻¹ := by
    intro h
    have hji : j = i := primeMellin_nodes_injective p hp h
    exact (ne_of_gt hlt) hji
  exact sub_ne_zero.mpr hneq

/-- Doubled block lift of a matrix, organized as a block diagonal stage. -/
noncomputable def doubledLift (V : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℝ :=
  Matrix.blockDiagonal fun _ : Bool => V

lemma det_doubledLift (V : Matrix (Fin n) (Fin n) ℝ) :
    det (doubledLift V) = (det V)^2 := by
  simp [doubledLift, Matrix.det_blockDiagonal]

lemma det_doubledLift_ne_zero (V : Matrix (Fin n) (Fin n) ℝ) (hV : det V ≠ 0) :
    det (doubledLift V) ≠ 0 := by
  rw [det_doubledLift]
  exact pow_ne_zero 2 hV

/--
Orthogonal matrices preserve the Euclidean contraction that encodes the
Majorana anticommutator.
-/
lemma anticommutator_orthogonality_invariant
    (O : Matrix (Fin n) (Fin n) ℝ) (hO : O * O.transpose = 1) (i j : Fin n) :
    ∑ k, O i k * O j k = if i = j then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hO
  simpa [Matrix.mul_apply, Matrix.transpose_apply] using h

end PrimeMellinSymplecticCAR
