/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.Pin55NondegenerateKreinBridge
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.Real
import Mathlib.Tactic

namespace InfoGeometry.Lie.SO55GlobalConformalPrecursors

open Matrix InfoGeometry.Lie.Pin55NondegenerateKreinBridge

local instance : LieRing (Matrix (Fin 10) (Fin 10) ℝ) := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ (Matrix (Fin 10) (Fin 10) ℝ) := LieAlgebra.ofAssociativeAlgebra

set_option maxHeartbeats 2000000

/-- Explicit expansion of a summation over `Fin 10` into 10 terms. -/
lemma sum_fin10 {α : Type*} [AddCommMonoid α] (f : Fin 10 → α) :
    (∑ i : Fin 10, f i) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  repeat rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_zero, add_zero]
  simp only [add_assoc]
  rfl

/-- Definition of a group element in $SO(5,5)$: a matrix $M \in M_{10}(\mathbb{R})$
preserving the signature $(5,5)$ Krein metric $J_{5,5}$ and having determinant $1$. -/
def IsSO55GroupMatrix (M : Matrix (Fin 10) (Fin 10) ℝ) : Prop :=
  Mᵀ * J55 * M = J55 ∧ M.det = 1

/-- The identity matrix belongs to $SO(5,5)$. -/
theorem isSO55_one : IsSO55GroupMatrix 1 := by
  dsimp [IsSO55GroupMatrix]
  refine ⟨?_, det_one⟩
  rw [transpose_one, Matrix.one_mul, Matrix.mul_one]

/-- The group $SO(5,5)$ is closed under matrix multiplication. -/
theorem isSO55_mul {M₁ M₂ : Matrix (Fin 10) (Fin 10) ℝ}
    (h₁ : IsSO55GroupMatrix M₁) (h₂ : IsSO55GroupMatrix M₂) :
    IsSO55GroupMatrix (M₁ * M₂) := by
  dsimp [IsSO55GroupMatrix] at *
  refine ⟨?_, ?_⟩
  · calc (M₁ * M₂)ᵀ * J55 * (M₁ * M₂)
      _ = M₂ᵀ * (M₁ᵀ * J55 * M₁) * M₂ := by
        rw [transpose_mul]
        simp only [mul_assoc]
      _ = M₂ᵀ * J55 * M₂ := by rw [h₁.1]
      _ = J55 := h₂.1
  · rw [det_mul, h₁.2, h₂.2, mul_one]

/-- Any $M \in SO(5,5)$ is an isometry of the signature $(5,5)$ Krein form:
$\langle M x, M y \rangle_{5,5} = \langle x, y \rangle_{5,5}$. -/
theorem isSO55_isometry (M : Matrix (Fin 10) (Fin 10) ℝ) (hM : IsSO55GroupMatrix M)
    (x y : Fin 10 → ℝ) :
    kreinForm55 (M.mulVec x) (M.mulVec y) = kreinForm55 x y := by
  dsimp [kreinForm55]
  have h1 : (M *ᵥ x) ⬝ᵥ (J55 *ᵥ (M *ᵥ y)) = x ⬝ᵥ ((Mᵀ * J55 * M) *ᵥ y) := by
    rw [← vecMul_transpose]
    rw [← dotProduct_mulVec]
    rw [mulVec_mulVec, mulVec_mulVec]
  rw [h1, hM.1]

/-- Non-degeneracy of $J_{5,5}$ determinant: $\det(J_{5,5}) \ne 0$. -/
theorem det_J55_ne_zero : (J55 : Matrix (Fin 10) (Fin 10) ℝ).det ≠ 0 := by
  intro h
  have h_sq := J55_mul_self
  have h_det := congrArg Matrix.det h_sq
  rw [Matrix.det_mul, Matrix.det_one] at h_det
  rw [h, MulZeroClass.zero_mul] at h_det
  norm_num at h_det

/-- Explicit 1-parameter hyperbolic boost subgroup $\Lambda(\xi)$ in the $(0, 5)$ timelike/spacelike plane. -/
noncomputable def so55Boost (ξ : ℝ) : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j =>
    if i = 0 ∧ j = 0 then Real.cosh ξ
    else if i = 0 ∧ j = 5 then Real.sinh ξ
    else if i = 5 ∧ j = 0 then Real.sinh ξ
    else if i = 5 ∧ j = 5 then Real.cosh ξ
    else if i = j then 1
    else 0

/-- The boost family satisfies the 1-parameter group homomorphism $\Lambda(\xi_1 + \xi_2) = \Lambda(\xi_1) \Lambda(\xi_2)$. -/
theorem so55Boost_add (ξ₁ ξ₂ : ℝ) :
    so55Boost (ξ₁ + ξ₂) = so55Boost ξ₁ * so55Boost ξ₂ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    rw [Matrix.mul_apply, sum_fin10]
    dsimp [so55Boost]
    first
    | (simp only [Real.cosh_add, Real.sinh_add]; ring)
    | ring
  }

/-- Hyperbolic identity: $\cosh^2 \xi - \sinh^2 \xi = 1$ in the exact expanded 10-term summation form. -/
lemma cosh_sq_sub_sinh_sq_add_neg (ξ : ℝ) :
    Real.cosh ξ * 1 * Real.cosh ξ + 0 * 1 * 0 + 0 * 1 * 0 + 0 * 1 * 0 + 0 * 1 * 0 +
    Real.sinh ξ * -1 * Real.sinh ξ + 0 * -1 * 0 + 0 * -1 * 0 + 0 * -1 * 0 + 0 * -1 * 0 = 1 := by
  calc Real.cosh ξ * 1 * Real.cosh ξ + 0 * 1 * 0 + 0 * 1 * 0 + 0 * 1 * 0 + 0 * 1 * 0 +
       Real.sinh ξ * -1 * Real.sinh ξ + 0 * -1 * 0 + 0 * -1 * 0 + 0 * -1 * 0 + 0 * -1 * 0
    _ = Real.cosh ξ ^ 2 - Real.sinh ξ ^ 2 := by ring
    _ = 1 := Real.cosh_sq_sub_sinh_sq ξ

/-- Hyperbolic identity: $\sinh^2 \xi - \cosh^2 \xi = -1$ in the exact expanded 10-term summation form. -/
lemma sinh_sq_sub_cosh_sq_add_neg (ξ : ℝ) :
    Real.sinh ξ * 1 * Real.sinh ξ + 0 * 1 * 0 + 0 * 1 * 0 + 0 * 1 * 0 + 0 * 1 * 0 +
    Real.cosh ξ * -1 * Real.cosh ξ + 0 * -1 * 0 + 0 * -1 * 0 + 0 * -1 * 0 + 0 * -1 * 0 = -1 := by
  calc Real.sinh ξ * 1 * Real.sinh ξ + 0 * 1 * 0 + 0 * 1 * 0 + 0 * 1 * 0 + 0 * 1 * 0 +
       Real.cosh ξ * -1 * Real.cosh ξ + 0 * -1 * 0 + 0 * -1 * 0 + 0 * -1 * 0 + 0 * -1 * 0
    _ = - (Real.cosh ξ ^ 2 - Real.sinh ξ ^ 2) := by ring
    _ = -1 := by rw [Real.cosh_sq_sub_sinh_sq]

/-- Action of post-multiplying $(so55Boost ξ)ᵀ$ by the diagonal matrix $J_{5,5}$. -/
lemma so55Boost_transpose_mul_J55_apply (ξ : ℝ) (i k : Fin 10) :
    ((so55Boost ξ)ᵀ * J55) i k = so55Boost ξ k i * (if k.val < 5 then 1 else -1) := by
  dsimp [J55]
  rw [mul_diagonal_apply, transpose_apply]

/-- The hyperbolic boost preserves the signature $(5,5)$ Krein metric: $\Lambda(\xi)^T J_{5,5} \Lambda(\xi) = J_{5,5}$. -/
theorem so55Boost_krein (ξ : ℝ) :
    (so55Boost ξ)ᵀ * J55 * so55Boost ξ = J55 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals {
    rw [Matrix.mul_apply, sum_fin10]
    simp_rw [so55Boost_transpose_mul_J55_apply]
    dsimp [so55Boost, J55, Matrix.diagonal]
    first
    | exact cosh_sq_sub_sinh_sq_add_neg ξ
    | exact sinh_sq_sub_cosh_sq_add_neg ξ
    | ring
  }

/-- The determinant of the hyperbolic boost is identically $1$. -/
theorem so55Boost_det (ξ : ℝ) : (so55Boost ξ).det = 1 := by
  have h_add := so55Boost_add (ξ / 2) (ξ / 2)
  have h_half : ξ / 2 + ξ / 2 = ξ := by ring
  rw [h_half] at h_add
  have h_det_sq : (so55Boost ξ).det = (so55Boost (ξ / 2)).det ^ 2 := by
    rw [h_add, det_mul, sq]
  have h_nonneg : 0 ≤ (so55Boost ξ).det := by
    rw [h_det_sq]
    exact sq_nonneg _
  have h_krein := so55Boost_krein ξ
  have h_det_krein := congrArg Matrix.det h_krein
  rw [det_mul, det_mul, det_transpose] at h_det_krein
  have h_det_J_ne := det_J55_ne_zero
  have h_sq_one : (so55Boost ξ).det ^ 2 = 1 := by
    have h_cancel : ((so55Boost ξ).det ^ 2 - 1) * J55.det = 0 := by
      calc
        ((so55Boost ξ).det ^ 2 - 1) * J55.det
          = ((so55Boost ξ).det * J55.det * (so55Boost ξ).det) - J55.det := by ring
        _ = J55.det - J55.det := by rw [h_det_krein]
        _ = 0 := sub_self _
    cases mul_eq_zero.mp h_cancel with
    | inl h1 =>
      linear_combination h1
    | inr h2 =>
      exact False.elim (h_det_J_ne h2)
  have h_factor : ((so55Boost ξ).det - 1) * ((so55Boost ξ).det + 1) = 0 := by
    calc
      ((so55Boost ξ).det - 1) * ((so55Boost ξ).det + 1)
        = (so55Boost ξ).det ^ 2 - 1 := by ring
      _ = 1 - 1 := by rw [h_sq_one]
      _ = 0 := sub_self _
  cases mul_eq_zero.mp h_factor with
  | inl h1 =>
    exact sub_eq_zero.mp h1
  | inr h2 =>
    have h_contra : (so55Boost ξ).det + 1 > 0 := by
      linarith
    linarith

/-- The hyperbolic boost is a member of the global Lie group $SO(5,5)$. -/
theorem so55Boost_isSO55 (ξ : ℝ) : IsSO55GroupMatrix (so55Boost ξ) :=
  ⟨so55Boost_krein ξ, so55Boost_det ξ⟩

/-- $\frac{1}{2} e^x \le \cosh x$ for all $x \in \mathbb{R}$. -/
theorem exp_half_le_cosh (x : ℝ) : Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have h_pos : 0 ≤ Real.exp (-x) / 2 := by
    positivity
  linarith

/-- Hyperbolic cosine diverges to $+\infty$ as $x \to +\infty$. -/
theorem tendsto_cosh_atTop : Filter.Tendsto Real.cosh Filter.atTop Filter.atTop := by
  have h_div := Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2) Real.tendsto_exp_atTop
  exact Filter.tendsto_atTop_mono exp_half_le_cosh h_div

/-- The hyperbolic boost subgroup is unbounded in the operator/entry norm as $\xi \to +\infty$,
certifying that the global group $SO(5,5)$ is non-compact. -/
theorem so55Boost_unbounded : Filter.Tendsto (fun ξ : ℝ => so55Boost ξ 0 0) Filter.atTop Filter.atTop := by
  have h_eq : (fun ξ : ℝ => so55Boost ξ 0 0) = Real.cosh := by
    ext ξ
    rfl
  rw [h_eq]
  exact tendsto_cosh_atTop

/-- Conformal null quadric in $\mathbb{R}^{5,5}$: the locus of non-zero null vectors with respect to $\langle \cdot, \cdot \rangle_{5,5}$. -/
def NullQuadric : Set (Fin 10 → ℝ) := { x | x ≠ 0 ∧ kreinForm55 x x = 0 }

/-- The conformal null quadric is invariant under the action of the global group $SO(5,5)$. -/
theorem nullQuadric_invariant (M : Matrix (Fin 10) (Fin 10) ℝ) (hM : IsSO55GroupMatrix M)
    {x : Fin 10 → ℝ} (hx : x ∈ NullQuadric) : M.mulVec x ∈ NullQuadric := by
  dsimp [NullQuadric] at *
  refine ⟨?_, ?_⟩
  · intro h_zero
    let N : Matrix (Fin 10) (Fin 10) ℝ := J55 * Mᵀ * J55
    have h_inv : N * M = 1 := by
      calc N * M
        _ = (J55 * Mᵀ * J55) * M := rfl
        _ = J55 * (Mᵀ * J55 * M) := by simp only [mul_assoc]
        _ = J55 * J55 := by rw [hM.1]
        _ = 1 := J55_mul_self
    have h_x_zero : x = 0 := by
      calc x
        _ = (1 : Matrix (Fin 10) (Fin 10) ℝ).mulVec x := by rw [one_mulVec]
        _ = (N * M).mulVec x := by rw [h_inv]
        _ = N.mulVec (M.mulVec x) := by rw [mulVec_mulVec]
        _ = N.mulVec 0 := by rw [h_zero]
        _ = 0 := mulVec_zero N
    exact hx.1 h_x_zero
  · rw [isSO55_isometry M hM x x]
    exact hx.2

/-- Parabolic CFT 3-grading: Dilatation generator $D = E_{0,5} + E_{5,0}$. -/
def genD : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j =>
    if i = 0 ∧ j = 5 then 1
    else if i = 5 ∧ j = 0 then 1
    else 0

/-- Dilatation generator belongs to $\mathfrak{so}(5,5)$: $D^T J_{5,5} + J_{5,5} D = 0$. -/
theorem genD_isSO55 : IsSO55KreinMatrix genD := by
  dsimp [IsSO55KreinMatrix, J55]
  ext i j
  rw [Matrix.add_apply, mul_diagonal_apply, diagonal_mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
  dsimp [genD]
  fin_cases i <;> fin_cases j <;> norm_num

/-- Parabolic CFT 3-grading: Translation generator for transverse coordinate $k$ ($0 < k < 5$):
$P_k = (E_{0,k} - E_{k,0}) + (E_{5,k} + E_{k,5})$. -/
def genP (k : Fin 10) : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j =>
    if i = 0 ∧ j = k then 1
    else if i = k ∧ j = 0 then -1
    else if i = 5 ∧ j = k then 1
    else if i = k ∧ j = 5 then 1
    else 0

/-- Translation generator belongs to $\mathfrak{so}(5,5)$. -/
theorem genP_isSO55 (k : Fin 10) (hk : 0 < k.val ∧ k.val < 5) : IsSO55KreinMatrix (genP k) := by
  dsimp [IsSO55KreinMatrix, J55]
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    revert k hk
    decide
  rcases hk_cases with rfl | rfl | rfl | rfl
  all_goals {
    ext i j
    rw [Matrix.add_apply, mul_diagonal_apply, diagonal_mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
    dsimp [genP]
    fin_cases i <;> fin_cases j <;> norm_num
  }

/-- Parabolic CFT 3-grading: Special conformal generator for transverse coordinate $k$ ($0 < k < 5$):
$K_k = -(E_{0,k} - E_{k,0}) + (E_{5,k} + E_{k,5})$. -/
def genK (k : Fin 10) : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j =>
    if i = 0 ∧ j = k then -1
    else if i = k ∧ j = 0 then 1
    else if i = 5 ∧ j = k then 1
    else if i = k ∧ j = 5 then 1
    else 0

/-- Special conformal generator belongs to $\mathfrak{so}(5,5)$. -/
theorem genK_isSO55 (k : Fin 10) (hk : 0 < k.val ∧ k.val < 5) : IsSO55KreinMatrix (genK k) := by
  dsimp [IsSO55KreinMatrix, J55]
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    revert k hk
    decide
  rcases hk_cases with rfl | rfl | rfl | rfl
  all_goals {
    ext i j
    rw [Matrix.add_apply, mul_diagonal_apply, diagonal_mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
    dsimp [genK]
    fin_cases i <;> fin_cases j <;> norm_num
  }

/-- Conformal weight $+1$ eigenvalue equation: $\⁅D, P_k⁆ = P_k$. -/
theorem bracket_genD_genP (k : Fin 10) (hk : 0 < k.val ∧ k.val < 5) : ⁅genD, genP k⁆ = genP k := by
  change genD * genP k - genP k * genD = genP k
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    revert k hk
    decide
  rcases hk_cases with rfl | rfl | rfl | rfl
  all_goals {
    ext i j
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, sum_fin10, sum_fin10]
    dsimp [genD, genP]
    fin_cases i <;> fin_cases j <;> norm_num
  }

/-- Conformal weight $-1$ eigenvalue equation: $\⁅D, K_k⁆ = - K_k$. -/
theorem bracket_genD_genK (k : Fin 10) (hk : 0 < k.val ∧ k.val < 5) : ⁅genD, genK k⁆ = - genK k := by
  change genD * genK k - genK k * genD = - genK k
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    revert k hk
    decide
  rcases hk_cases with rfl | rfl | rfl | rfl
  all_goals {
    ext i j
    rw [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply, Matrix.mul_apply, sum_fin10, sum_fin10]
    dsimp [genD, genK]
    fin_cases i <;> fin_cases j <;> norm_num
  }

/-- Canonical square matrix $P_k^2 = -E_{0,0} + E_{0,5} - E_{5,0} + E_{5,5}$, identical for all transverse coordinates. -/
def genP_sq_matrix : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j =>
    if i = 0 ∧ j = 0 then -1
    else if i = 0 ∧ j = 5 then 1
    else if i = 5 ∧ j = 0 then -1
    else if i = 5 ∧ j = 5 then 1
    else 0

/-- The square $P_k^2$ equals the transverse-independent canonical matrix. -/
lemma genP_sq_eq (k : Fin 10) (hk : 0 < k.val ∧ k.val < 5) : genP k * genP k = genP_sq_matrix := by
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    revert k hk
    decide
  rcases hk_cases with rfl | rfl | rfl | rfl
  all_goals {
    ext i j
    rw [Matrix.mul_apply, sum_fin10]
    dsimp [genP, genP_sq_matrix]
    fin_cases i <;> fin_cases j <;> norm_num
  }

/-- Product of the canonical square matrix with $P_k$ vanishes identically. -/
lemma genP_sq_mul_genP (k : Fin 10) (hk : 0 < k.val ∧ k.val < 5) : genP_sq_matrix * genP k = 0 := by
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    revert k hk
    decide
  rcases hk_cases with rfl | rfl | rfl | rfl
  all_goals {
    ext i j
    rw [Matrix.mul_apply, sum_fin10]
    dsimp [genP_sq_matrix, genP, Matrix.zero_apply]
    fin_cases i <;> fin_cases j <;> norm_num
  }

/-- Parabolic translation nilpotency of order 3: $P_k^3 = 0$. -/
theorem genP_nilpotent3 (k : Fin 10) (hk : 0 < k.val ∧ k.val < 5) : (genP k) ^ 3 = 0 := by
  calc (genP k) ^ 3
    _ = (genP k * genP k) * genP k := by rw [pow_succ, sq, mul_assoc]
    _ = genP_sq_matrix * genP k := by rw [genP_sq_eq k hk]
    _ = 0 := genP_sq_mul_genP k hk

/-- OpenGauss Trap T16 Non-Commutativity Witness: $D P_1 \ne P_1 D$. -/
theorem genD_mul_genP_ne (h1 : 0 < (1 : Fin 10).val ∧ (1 : Fin 10).val < 5) :
    genD * genP ⟨1, by decide⟩ ≠ genP ⟨1, by decide⟩ * genD := by
  intro h
  have h_br := bracket_genD_genP ⟨1, by decide⟩ h1
  change genD * genP ⟨1, by decide⟩ - genP ⟨1, by decide⟩ * genD = genP ⟨1, by decide⟩ at h_br
  rw [h, sub_self] at h_br
  have h_entry := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℝ => M 0 1) h_br.symm
  dsimp [genP, Matrix.zero_apply] at h_entry
  norm_num at h_entry

end InfoGeometry.Lie.SO55GlobalConformalPrecursors
