/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- Polar Decomposition via Newton-Schulz Iteration -/
/- The Newton-Schulz iteration computes the unitary factor U = msign(G) of the polar decomposition
   G = P * U without requiring a full SVD. Uses only matrix addition, transposition, and inversion. -/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix
open scoped Matrix

namespace InfoGeometry.Optimization

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One step of the generalized Newton-Schulz iteration for Polar Decomposition. -/
noncomputable def PolarNewtonStep (X X_inv : Matrix n n ℝ) : Matrix n n ℝ :=
  (1/2 : ℝ) • (X + X_invᵀ)

/-- The formal structure of the Polar Decomposition G = P * U -/
structure PolarDecomposition (G : Matrix n n ℝ) where
  U : Matrix n n ℝ  -- The unitary factor (msign(G))
  P : Matrix n n ℝ  -- The positive semidefinite factor
  decomp : G = P * U
  unitary : U * Uᵀ = 1
  self_adjoint : Pᵀ = P

/--
  If the Newton iteration converges to a fixed point U, U must be orthogonal.
  X_{k+1} = X_k ⟹ U = 1/2(U + U^{-T}) ⟹ U = U^{-T} ⟹ U * Uᵀ = I.
-/
theorem polar_newton_limit_unitary (U U_inv : Matrix n n ℝ)
    (h_inv : U * U_inv = 1) (h_fixed : PolarNewtonStep U U_inv = U) :
    U * Uᵀ = 1 := by
  have h_transpose_inv : Uᵀ = U_inv := by
    ext i j
    have hij := congrFun (congrFun h_fixed j) i
    simp [PolarNewtonStep] at hij
    have hij₂ : U j i + U_inv i j = 2 * U j i := by
      have hmul := congrArg (fun x : ℝ => (2 : ℝ) * x) hij
      norm_num [mul_add, mul_assoc] at hmul
      simpa [two_mul] using hmul
    simpa using (by linarith : U j i = U_inv i j)
  calc
    U * Uᵀ = U * U_inv := by rw [h_transpose_inv]
    _ = 1 := h_inv

/-! ## Explicit left polar decomposition in dimension two -/

abbrev RealMat2 := Matrix (Fin 2) (Fin 2) ℝ

private lemma ext_realMat2 {A B : RealMat2}
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

private lemma det_realMat2 (M : RealMat2) :
    Matrix.det M = M 0 0 * M 1 1 - M 0 1 * M 1 0 := Matrix.det_fin_two M

/-- The positive scalar denominator in the explicit rotation factor. -/
noncomputable def polarScale2 (M : RealMat2) : ℝ :=
  Real.sqrt ((M 0 0 + M 1 1) ^ 2 + (M 0 1 - M 1 0) ^ 2)

/-- A two-dimensional rotation matrix in scalar coordinates. -/
def rotation2 (a b : ℝ) : RealMat2 := ![![a, b], ![-b, a]]

/-- The standard rotation matrix is orthogonal whenever its coordinates lie on the unit circle. -/
lemma rotation2_orth {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    (rotation2 a b)ᵀ * rotation2 a b = 1 := by
  apply ext_realMat2
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change a * a + (-b) * (-b) = 1
    nlinarith
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change a * b + (-b) * a = 0
    ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change b * a + a * (-b) = 0
    ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change b * b + a * a = 1
    nlinarith

lemma rotation2_right_orth {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    rotation2 a b * (rotation2 a b)ᵀ = 1 := by
  apply ext_realMat2
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change a * a + b * b = 1
    nlinarith
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change a * (-b) + b * a = 0
    ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (-b) * a + a * b = 0
    ring
  · rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (-b) * (-b) + a * a = 1
    nlinarith

lemma rotation2_det (a b : ℝ) : Matrix.det (rotation2 a b) = a ^ 2 + b ^ 2 := by
  rw [det_realMat2]
  change a * a - b * (-b) = a ^ 2 + b ^ 2
  ring

/-- The compact factor in the left polar decomposition `M = K P`. -/
noncomputable def polarK2 (M : RealMat2) : RealMat2 :=
  let τ := polarScale2 M
  rotation2 ((M 0 0 + M 1 1) / τ) ((M 0 1 - M 1 0) / τ)

/-- The explicit compact factor is orthogonal for every positive-determinant matrix. -/
lemma polarK2_orth {M : RealMat2} (hdet : 0 < Matrix.det M) :
    (polarK2 M)ᵀ * polarK2 M = 1 := by
  let x := M 0 0 + M 1 1
  let y := M 0 1 - M 1 0
  let τ := polarScale2 M
  have hτ_pos : 0 < τ := by
    dsimp [τ, polarScale2]
    apply Real.sqrt_pos.mpr
    rw [det_realMat2] at hdet
    nlinarith [sq_nonneg (M 0 0 - M 1 1), sq_nonneg (M 0 1 + M 1 0)]
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
  have hτ_sq : τ ^ 2 = x ^ 2 + y ^ 2 := by
    dsimp [τ, x, y, polarScale2]
    exact Real.sq_sqrt (by positivity)
  apply rotation2_orth
  have hdiv : (x / τ) ^ 2 + (y / τ) ^ 2 = (x ^ 2 + y ^ 2) / τ ^ 2 := by
    field_simp
  rw [hdiv, hτ_sq]
  have hnum : x ^ 2 + y ^ 2 ≠ 0 := by rw [← hτ_sq]; exact pow_ne_zero 2 hτ_ne
  exact div_self hnum

lemma polarK2_right_orth {M : RealMat2} (hdet : 0 < Matrix.det M) :
    polarK2 M * (polarK2 M)ᵀ = 1 := by
  let x := M 0 0 + M 1 1
  let y := M 0 1 - M 1 0
  let τ := polarScale2 M
  have hτ_pos : 0 < τ := by
    dsimp [τ, polarScale2]
    apply Real.sqrt_pos.mpr
    rw [det_realMat2] at hdet
    nlinarith [sq_nonneg (M 0 0 - M 1 1), sq_nonneg (M 0 1 + M 1 0)]
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
  have hτ_sq : τ ^ 2 = x ^ 2 + y ^ 2 := by
    dsimp [τ, x, y, polarScale2]
    exact Real.sq_sqrt (by positivity)
  have hcircle : (x / τ) ^ 2 + (y / τ) ^ 2 = 1 := by
    have hdiv : (x / τ) ^ 2 + (y / τ) ^ 2 = (x ^ 2 + y ^ 2) / τ ^ 2 := by field_simp
    rw [hdiv, ← hτ_sq]
    exact div_self (pow_ne_zero 2 hτ_ne)
  change rotation2 (x / τ) (y / τ) * (rotation2 (x / τ) (y / τ))ᵀ = 1
  exact rotation2_right_orth hcircle

lemma polarK2_det {M : RealMat2} (hdet : 0 < Matrix.det M) :
    Matrix.det (polarK2 M) = 1 := by
  let x := M 0 0 + M 1 1
  let y := M 0 1 - M 1 0
  let τ := polarScale2 M
  have hτ_pos : 0 < τ := by
    dsimp [τ, polarScale2]
    apply Real.sqrt_pos.mpr
    rw [det_realMat2] at hdet
    nlinarith [sq_nonneg (M 0 0 - M 1 1), sq_nonneg (M 0 1 + M 1 0)]
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
  have hτ_sq : τ ^ 2 = x ^ 2 + y ^ 2 := by
    dsimp [τ, x, y, polarScale2]
    exact Real.sq_sqrt (by positivity)
  have hcircle : (x / τ) ^ 2 + (y / τ) ^ 2 = 1 := by
    have hdiv : (x / τ) ^ 2 + (y / τ) ^ 2 = (x ^ 2 + y ^ 2) / τ ^ 2 := by field_simp
    rw [hdiv, ← hτ_sq]
    exact div_self (pow_ne_zero 2 hτ_ne)
  change Matrix.det (rotation2 (x / τ) (y / τ)) = 1
  rw [rotation2_det, hcircle]

/-- The stretch factor `P = Kᵀ M` in the left polar decomposition. -/
noncomputable def polarP2 (M : RealMat2) : RealMat2 := (polarK2 M)ᵀ * M

private lemma polarP2_offdiag_eq {M : RealMat2} : polarP2 M 0 1 = polarP2 M 1 0 := by
  rw [polarP2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Fin.sum_univ_two]
  dsimp [polarK2, rotation2]
  change ((M 0 0 + M 1 1) / polarScale2 M) * M 0 1 +
      -((M 0 1 - M 1 0) / polarScale2 M) * M 1 1 =
    ((M 0 1 - M 1 0) / polarScale2 M) * M 0 0 +
      ((M 0 0 + M 1 1) / polarScale2 M) * M 1 0
  field_simp
  ring

private lemma polarP2_00_formula {M : RealMat2} :
    polarP2 M 0 0 =
      ((M 0 0 + M 1 1) * M 0 0 - (M 0 1 - M 1 0) * M 1 0) /
        polarScale2 M := by
  rw [polarP2, Matrix.mul_apply, Fin.sum_univ_two]
  dsimp [polarK2, rotation2]
  change ((M 0 0 + M 1 1) / polarScale2 M) * M 0 0 +
      -((M 0 1 - M 1 0) / polarScale2 M) * M 1 0 = _
  field_simp
  ring

/-- The leading diagonal entry of the stretch is strictly positive when `det M > 0`. -/
lemma polarP2_00_pos {M : RealMat2} (hdet : 0 < Matrix.det M) :
    0 < polarP2 M 0 0 := by
  have hτ : 0 < polarScale2 M := by
    apply Real.sqrt_pos.mpr
    rw [det_realMat2] at hdet
    nlinarith [sq_nonneg (M 0 0 - M 1 1), sq_nonneg (M 0 1 + M 1 0)]
  rw [polarP2_00_formula]
  apply div_pos
  · rw [det_realMat2] at hdet
    nlinarith [sq_nonneg (M 0 0), sq_nonneg (M 1 0)]
  · exact hτ

/-- The explicit stretch factor is symmetric for every real `2 × 2` matrix. -/
lemma polarP2_symmetric (M : RealMat2) : (polarP2 M)ᵀ = polarP2 M := by
  apply ext_realMat2
  · rfl
  · change polarP2 M 1 0 = polarP2 M 0 1
    exact (polarP2_offdiag_eq (M := M)).symm
  · change polarP2 M 0 1 = polarP2 M 1 0
    exact polarP2_offdiag_eq (M := M)
  · rfl

/-- The explicit factors reconstruct every positive-determinant `2 × 2` matrix. -/
lemma polarK2_mul_polarP2 {M : RealMat2} (hdet : 0 < Matrix.det M) :
    polarK2 M * polarP2 M = M := by
  rw [polarP2, ← Matrix.mul_assoc, polarK2_right_orth hdet, one_mul]

/-- The explicit stretch has the same determinant as the input matrix. -/
lemma polarP2_det {M : RealMat2} (hdet : 0 < Matrix.det M) :
    Matrix.det (polarP2 M) = Matrix.det M := by
  rw [polarP2, Matrix.det_mul, Matrix.det_transpose, polarK2_det hdet, one_mul]

/-- The explicit stretch is positive definite for every positive-determinant input. -/
lemma polarP2_posDef {M : RealMat2} (hdet : 0 < Matrix.det M) :
    (polarP2 M).PosDef := by
  have hsymm := polarP2_symmetric M
  have hp : 0 < polarP2 M 0 0 := polarP2_00_pos hdet
  have hdetP : 0 < Matrix.det (polarP2 M) := by
    rw [polarP2_det hdet]
    exact hdet
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change Matrix.transpose ((polarP2 M).map star) = polarP2 M
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, star_trivial]
    exact congrFun (congrFun hsymm i) j
  · intro v hv
    let a := v 0
    let b := v 1
    let p := polarP2 M 0 0
    let q := polarP2 M 0 1
    let r := polarP2 M 1 1
    have hq : polarP2 M 1 0 = q := by
      have h := congrFun (congrFun hsymm 1) 0
      change polarP2 M 0 1 = polarP2 M 1 0 at h
      exact h.symm
    have hdet_eq : Matrix.det (polarP2 M) = p * r - q * q := by
      rw [det_realMat2]
      dsimp [p, q, r]
      rw [hq]
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      rcases not_or.mp h with ⟨ha, hb⟩
      apply hv
      funext i
      fin_cases i
      · exact not_ne_iff.mp ha
      · exact not_ne_iff.mp hb
    have hquad : star v ⬝ᵥ (polarP2 M *ᵥ v) =
        p * a ^ 2 + q * a * b + q * a * b + r * b ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, a, b, p, q, r, hq]
      ring
    have hcomplete :
        (p * a + q * b) ^ 2 / p + (Matrix.det (polarP2 M) / p) * b ^ 2 =
          p * a ^ 2 + q * a * b + q * a * b + r * b ^ 2 := by
      rw [hdet_eq]
      have hp_ne : p ≠ 0 := ne_of_gt hp
      field_simp [hp_ne]
      ring
    rw [hquad, ← hcomplete]
    by_cases hb : b = 0
    · have ha : a ≠ 0 := by
        rcases hab with ha | hbne
        · exact ha
        · exact (hbne hb).elim
      have hfirst : 0 < (p * a + q * 0) ^ 2 / p := by
        apply div_pos
        · apply sq_pos_of_ne_zero
          simpa using mul_ne_zero (ne_of_gt hp) ha
        · exact hp
      rw [hb]
      simpa using hfirst
    · have hfirst : 0 ≤ (p * a + q * b) ^ 2 / p :=
        div_nonneg (sq_nonneg _) (le_of_lt hp)
      have hsecond : 0 < (Matrix.det (polarP2 M) / p) * b ^ 2 :=
        mul_pos (div_pos hdetP hp) (sq_pos_of_ne_zero hb)
      exact add_pos_of_nonneg_of_pos hfirst hsecond

/-- The square of the explicit stretch factor is the Gram matrix. -/
lemma polarP2_sq_gram {M : RealMat2} (hdet : 0 < Matrix.det M) :
    polarP2 M * polarP2 M = Mᵀ * M := by
  calc
    polarP2 M * polarP2 M = (polarP2 M)ᵀ * polarP2 M := by
      rw [polarP2_symmetric]
    _ = ((polarK2 M)ᵀ * M)ᵀ * ((polarK2 M)ᵀ * M) := by rw [polarP2]
    _ = Mᵀ * (polarK2 M * (polarK2 M)ᵀ) * M := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      noncomm_ring
    _ = Mᵀ * M := by rw [polarK2_right_orth hdet]; noncomm_ring

end InfoGeometry.Optimization

namespace InfoGeometry.OptimizationWitnesses

theorem realMat2_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let B : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have hAB : (A * B) 0 0 = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (1 : Fin 2)]
    · simp [A, B]
    · intro k _ hk
      simp [A, hk]
    · intro h1
      exact (h1 (Finset.mem_univ _)).elim
  have hBA : (B * A) 0 0 = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero (fun k _ => by simp [B])
  rw [hAB, hBA] at h00
  exact one_ne_zero h00

end InfoGeometry.OptimizationWitnesses
