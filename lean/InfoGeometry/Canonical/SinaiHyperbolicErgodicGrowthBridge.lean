import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge

open Matrix
open scoped Matrix
open Real
open InfoGeometry.Canonical.SinaiHyperbolicErgodicConeFieldBridge

namespace InfoGeometry.Canonical.SinaiHyperbolicErgodicGrowthBridge

/-! ### Finite Products of the repository-owned Sinai Jacobians

The product is non-autonomous in its input list. The quantitative theorem
below concerns the constant-parameter orbit on the already-defined unstable
eigenline; it makes no claim of uniform expansion for arbitrary varying
collision parameters. -/

def collisionChain : List (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ
  | [] => 1
  | (τ, κ) :: rest => sinaiJacobian τ κ * collisionChain rest

theorem collisionChain_replicate (τ κ : ℝ) (n : ℕ) :
    collisionChain (List.replicate n (τ, κ)) = sinaiJacobian τ κ ^ n := by
  induction n with
  | zero =>
    simp [collisionChain]
  | succ n ih =>
    simp only [List.replicate_succ, collisionChain, ih]
    rw [pow_succ']

theorem collisionChain_append (xs ys : List (ℝ × ℝ)) :
    collisionChain (xs ++ ys) = collisionChain xs * collisionChain ys := by
  induction xs with
  | nil => simp [collisionChain]
  | cons x xs ih =>
    rcases x with ⟨τ, κ⟩
    simp only [List.cons_append, collisionChain, ih]
    rw [mul_assoc]

/-! ### 3. Algebraic Action on Invariant Vectors -/

lemma mulVec_one' (v : Fin 2 → ℝ) :
    mulVec (1 : Matrix (Fin 2) (Fin 2) ℝ) v = v := by
  ext i
  fin_cases i
  · dsimp [mulVec, dotProduct, one_apply]
    simp only [Fin.sum_univ_two]
    simp
  · dsimp [mulVec, dotProduct, one_apply]
    simp only [Fin.sum_univ_two]
    simp

lemma mulVec_smul' (M : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (v : Fin 2 → ℝ) :
    mulVec M (c • v) = c • mulVec M v := by
  ext i
  fin_cases i
  · dsimp [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    simp only [Fin.sum_univ_two]
    ring
  · dsimp [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    simp only [Fin.sum_univ_two]
    ring

lemma mulVec_mul_matrix {M N : Matrix (Fin 2) (Fin 2) ℝ} {v : Fin 2 → ℝ} :
    mulVec (M * N) v = mulVec M (mulVec N v) := by
  ext i
  fin_cases i
  · dsimp [mulVec, dotProduct, Matrix.mul_apply]
    simp only [Fin.sum_univ_two]
    ring
  · dsimp [mulVec, dotProduct, Matrix.mul_apply]
    simp only [Fin.sum_univ_two]
    ring

theorem mulVec_pow_eigen {M : Matrix (Fin 2) (Fin 2) ℝ} {v : Fin 2 → ℝ} {L : ℝ}
    (h : mulVec M v = L • v) (n : ℕ) :
    mulVec (M ^ n) v = (L ^ n) • v := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, one_smul, mulVec_one']
  | succ n ih =>
    rw [pow_succ', mulVec_mul_matrix, ih, mulVec_smul', h, smul_smul, pow_succ']
    congr 1
    ring

/-! ### 4. Quantitative Spectral Bounds -/

lemma abs_lambdaU_eq {u : ℝ} (hu : 0 < u) :
    |lambdaU u| = (2 + u + Real.sqrt (u * (u + 4))) / 2 := by
  have hu4 : 0 < u * (u + 4) := mul_pos hu (by linarith)
  have h_neg : lambdaU u < 0 := by
    dsimp [lambdaU]
    have : 0 < Real.sqrt (u * (u + 4)) := Real.sqrt_pos.mpr hu4
    linarith
  rw [abs_of_neg h_neg]
  dsimp [lambdaU]
  ring

lemma abs_lambdaU_gt_one_add_sqrt {u : ℝ} (hu : 0 < u) :
    1 + Real.sqrt u < |lambdaU u| := by
  have h4u_le : 4 * u ≤ u * (u + 4) := by
    have : u * (u + 4) = 4 * u + u^2 := by ring
    rw [this]
    have : 0 ≤ u^2 := sq_nonneg u
    linarith
  have h_sqrt_le : Real.sqrt (4 * u) ≤ Real.sqrt (u * (u + 4)) :=
    Real.sqrt_le_sqrt h4u_le
  have h_sqrt4_mul : Real.sqrt (4 * u) = 2 * Real.sqrt u := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), (by norm_num : Real.sqrt 4 = 2)]
  rw [h_sqrt4_mul] at h_sqrt_le
  rw [abs_lambdaU_eq hu]
  linarith

theorem lyapunov_uniform_lower_bound_strict {τ κ τ_min κ_min : ℝ}
    (hτ_min : 0 < τ_min) (hκ_min : 0 < κ_min)
    (hτ : τ_min ≤ τ) (hκ : κ_min ≤ κ) :
    Real.log (1 + Real.sqrt (τ_min * κ_min)) < Real.log |lambdaU (τ * κ)| := by
  have hu_min_pos : 0 < τ_min * κ_min := mul_pos hτ_min hκ_min
  have hu_pos : 0 < τ * κ := mul_pos (by linarith) (by linarith)
  have h_u_le : τ_min * κ_min ≤ τ * κ := by nlinarith
  have h_spec := abs_lambdaU_gt_one_add_sqrt hu_pos
  have h_lt : 1 + Real.sqrt (τ_min * κ_min) < |lambdaU (τ * κ)| := by
    calc
      1 + Real.sqrt (τ_min * κ_min) ≤ 1 + Real.sqrt (τ * κ) := by
        have : Real.sqrt (τ_min * κ_min) ≤ Real.sqrt (τ * κ) := Real.sqrt_le_sqrt h_u_le
        linarith
      _ < |lambdaU (τ * κ)| := h_spec
  have h_arg_pos : 0 < 1 + Real.sqrt (τ_min * κ_min) := by
    have : 0 ≤ Real.sqrt (τ_min * κ_min) := Real.sqrt_nonneg _
    linarith
  exact Real.log_lt_log h_arg_pos h_lt

theorem lyapunov_uniform_lower_bound {τ κ τ_min κ_min : ℝ}
    (hτ_min : 0 < τ_min) (hκ_min : 0 < κ_min)
    (hτ : τ_min ≤ τ) (hκ : κ_min ≤ κ) :
    Real.log (1 + Real.sqrt (τ_min * κ_min)) ≤ Real.log |lambdaU (τ * κ)| :=
  le_of_lt (lyapunov_uniform_lower_bound_strict hτ_min hκ_min hτ hκ)

lemma abs_pow_eq (x : ℝ) (n : ℕ) : |x ^ n| = |x| ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, abs_mul, ih]

lemma pow_le_pow_of_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    have : 0 ≤ a ^ n := pow_nonneg ha n
    nlinarith

lemma norm_smul_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (v : E) :
    ‖c • v‖ = |c| * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs]

/-! ### 5. The Uniform Growth Theorem -/

theorem sinai_uniform_exponential_growth
    {τ κ τ_min κ_min : ℝ}
    (hτ_min : 0 < τ_min) (hκ_min : 0 < κ_min)
    (hτ : τ_min ≤ τ) (hκ : κ_min ≤ κ)
    (n : ℕ) {v : Fin 2 → ℝ} (hv : v ∈ Eu τ κ) :
    (1 + Real.sqrt (τ_min * κ_min)) ^ n * ‖v‖ ≤
      ‖mulVec (sinaiJacobian τ κ ^ n) v‖ := by
  have hu_min_pos : 0 < τ_min * κ_min := mul_pos hτ_min hκ_min
  have hu_pos : 0 < τ * κ := mul_pos (by linarith) (by linarith)
  have h_u_le : τ_min * κ_min ≤ τ * κ := by nlinarith
  have h_sqrt_le : Real.sqrt (τ_min * κ_min) ≤ Real.sqrt (τ * κ) := Real.sqrt_le_sqrt h_u_le
  have h_spec := abs_lambdaU_gt_one_add_sqrt hu_pos
  have h_base_le : 1 + Real.sqrt (τ_min * κ_min) ≤ |lambdaU (τ * κ)| := by
    calc 1 + Real.sqrt (τ_min * κ_min) ≤ 1 + Real.sqrt (τ * κ) := by linarith
         _ ≤ |lambdaU (τ * κ)| := le_of_lt h_spec

  have h_base_nonneg : 0 ≤ 1 + Real.sqrt (τ_min * κ_min) := by
    have : 0 ≤ Real.sqrt (τ_min * κ_min) := Real.sqrt_nonneg _
    linarith

  have h_pow_le : (1 + Real.sqrt (τ_min * κ_min)) ^ n ≤ |lambdaU (τ * κ)| ^ n :=
    pow_le_pow_of_le_of_nonneg h_base_nonneg h_base_le n

  rcases Submodule.mem_span_singleton.mp hv with ⟨c, rfl⟩
  have h_pow_action : mulVec (sinaiJacobian τ κ ^ n) (c • eigenvecU τ κ) =
      (c * (lambdaU (τ * κ) ^ n)) • eigenvecU τ κ := by
    rw [mulVec_smul', mulVec_pow_eigen
      (SinaiHyperbolicErgodicConeFieldBridge.sinaiJacobian_mulVec_eigenvecU
        (lt_of_lt_of_le hτ_min hτ) (lt_of_lt_of_le hκ_min hκ)),
      smul_smul, mul_comm c]

  rw [h_pow_action, norm_smul_real (c * lambdaU (τ * κ) ^ n), norm_smul_real c]
  rw [abs_mul, abs_pow_eq]

  have h_nonneg_scale : 0 ≤ |c| * ‖eigenvecU τ κ‖ := by positivity
  calc
    (1 + Real.sqrt (τ_min * κ_min)) ^ n * (|c| * ‖eigenvecU τ κ‖)
      ≤ (|lambdaU (τ * κ)| ^ n) * (|c| * ‖eigenvecU τ κ‖) := by
        nlinarith
    _ = |c| * (|lambdaU (τ * κ)| ^ n) * ‖eigenvecU τ κ‖ := by ring

theorem sinai_cocycle_growth
    {τ κ τ_min κ_min : ℝ}
    (hτ_min : 0 < τ_min) (hκ_min : 0 < κ_min)
    (hτ : τ_min ≤ τ) (hκ : κ_min ≤ κ)
    (n : ℕ) {v : Fin 2 → ℝ} (hv : v ∈ Eu τ κ) :
    (1 + Real.sqrt (τ_min * κ_min)) ^ n * ‖v‖ ≤
      ‖mulVec (collisionChain (List.replicate n (τ, κ))) v‖ := by
  rw [collisionChain_replicate]
  exact sinai_uniform_exponential_growth hτ_min hκ_min hτ hκ n hv

end InfoGeometry.Canonical.SinaiHyperbolicErgodicGrowthBridge
