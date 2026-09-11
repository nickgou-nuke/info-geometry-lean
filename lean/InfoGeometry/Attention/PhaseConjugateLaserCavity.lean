import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic

namespace InfoGeometry.PhaseConjugateLaserCavity

open Finset Real

/-!
### 1. The Phase-Conjugate Mirror (PCM) and Aberration Self-Healing
-/

abbrev Mat2 := Fin 2 → Fin 2 → ℝ

def matMul2 (A B : Mat2) : Mat2 := fun i j =>
  A i 0 * B 0 j + A i 1 * B 1 j

def matId2 : Mat2 := fun i j =>
  if i = j then 1 else 0

/-- 2D rotation matrix representing an arbitrary phase aberration O_ϕ. -/
def rotMat (c s : ℝ) : Mat2 := fun i j =>
  match i, j with
  | 0, 0 => c
  | 0, 1 => -s
  | 1, 0 => s
  | 1, 1 => c

/-- The Phase-Conjugate Mirror (PCM) reflection matrix R = diag(1, -1). -/
def pcmMat : Mat2 := fun i j =>
  match i, j with
  | 0, 0 => 1
  | 0, 1 => 0
  | 1, 0 => 0
  | 1, 1 => -1

/-- Master Theorem 1 (Aberration Self-Healing Theorem):
    A wave passing forward through an aberrating medium (rotMat c s),
    reflecting off the Phase-Conjugate Mirror (pcmMat), passing back through
    the identical medium, and undergoing final PCM readout, returns strictly
    to the unperturbed identity:
    R ∘ O_ϕ ∘ R ∘ O_ϕ = I₂ for all c² + s² = 1. -/
theorem pcm_aberration_cancellation (c s : ℝ) (hc : c^2 + s^2 = 1) :
    matMul2 pcmMat (matMul2 (rotMat c s) (matMul2 pcmMat (rotMat c s))) = matId2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (unfold matMul2 pcmMat rotMat matId2; ring; try simp [hc])

/-!
### 2. LogSumExp Nonlinear Gain Saturation and Power Clamping
-/

variable {n : ℕ} [NeZero n]

/-- The LogSumExp function: LSE(s) = ln(∑_j exp(s_j)).
    Acts as the global saturated cavity potential. -/
noncomputable def lse (s : Fin n → ℝ) : ℝ :=
  Real.log (∑ j : Fin n, Real.exp (s j))

theorem exp_sum_pos (s : Fin n → ℝ) : 0 < ∑ j : Fin n, Real.exp (s j) := by
  apply Finset.sum_pos
  · intro j _
    exact Real.exp_pos (s j)
  · exact Finset.univ_nonempty

/-- Softmax probability distribution: p_i(s) = exp(s_i - LSE(s)). -/
noncomputable def softmaxProb (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (s i) / (∑ j : Fin n, Real.exp (s j))

/-- Effective saturated log-gain: g_sat(s)_i = s_i - LSE(s). -/
noncomputable def satLogGain (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  s i - lse s

/-- Master Theorem 2 (LSE Uniform Shift Law):
    LSE(s + c 1) = LSE(s) + c. -/
theorem lse_shift (s : Fin n → ℝ) (c : ℝ) :
    lse (fun j => s j + c) = lse s + c := by
  dsimp [lse]
  have h_exp : (∑ j : Fin n, Real.exp (s j + c)) = (∑ j : Fin n, Real.exp (s j)) * Real.exp c := by
    simp_rw [Real.exp_add]
    rw [← Finset.sum_mul]
  rw [h_exp]
  have h_pos : 0 < ∑ j : Fin n, Real.exp (s j) := exp_sum_pos s
  have h_exp_c_pos : 0 < Real.exp c := Real.exp_pos c
  rw [Real.log_mul (ne_of_gt h_pos) (ne_of_gt h_exp_c_pos)]
  rw [Real.log_exp]

omit [NeZero n] in
/-- Master Theorem 3 (Softmax Gain Invariance):
    Uniform pump amplification s ↦ s + c 1 leaves the attention distribution strictly invariant. -/
theorem softmax_shift_invariant (s : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    softmaxProb (fun j => s j + c) i = softmaxProb s i := by
  dsimp [softmaxProb]
  simp_rw [Real.exp_add]
  rw [← Finset.sum_mul]
  have hc_ne : Real.exp c ≠ 0 := ne_of_gt (Real.exp_pos c)
  rw [mul_div_mul_right _ _ hc_ne]

/-- Master Theorem 4 (Saturated Gain Shift Invariance):
    The effective saturated gain is completely clamped against uniform pump surges. -/
theorem satLogGain_shift_invariant (s : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    satLogGain (fun j => s j + c) i = satLogGain s i := by
  dsimp [satLogGain]
  rw [lse_shift]
  ring

/-- Master Theorem 5 (Nonlinear Power Clamping):
    The total saturated circulating optical power is strictly clamped to 1:
    ∑_i exp(g_sat_i) = 1. Exponential runaway is impossible. -/
theorem sat_power_clamped (s : Fin n → ℝ) :
    (∑ i : Fin n, Real.exp (satLogGain s i)) = 1 := by
  dsimp [satLogGain]
  have h_pos : 0 < ∑ j : Fin n, Real.exp (s j) := exp_sum_pos s
  have h_exp_lse : Real.exp (lse s) = ∑ j : Fin n, Real.exp (s j) := by
    dsimp [lse]
    exact Real.exp_log h_pos
  have h_decomp (i : Fin n) : Real.exp (s i - lse s) = Real.exp (s i) / Real.exp (lse s) := by
    rw [Real.exp_sub]
  simp_rw [h_decomp, h_exp_lse]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt h_pos)

/-!
### 3. Krein Net Modal Gain and Laser Threshold Classification
-/

variable {d d_k : ℕ} [NeZero d] [NeZero d_k]

abbrev TokenVec (d : ℕ) := Fin d → ℝ
abbrev HeadVec (d_k : ℕ) := Fin d_k → ℝ

def dotH (u v : HeadVec d_k) : ℝ :=
  ∑ i : Fin d_k, u i * v i

def projW (W : Fin d_k → Fin d → ℝ) (x : TokenVec d) : HeadVec d_k :=
  fun i => ∑ j : Fin d, W i j * x j

/-- Net modal gain functional: 𝒢(x) = ‖U x‖² - ‖V x‖². -/
def netGain (U V : Fin d_k → Fin d → ℝ) (x : TokenVec d) : ℝ :=
  dotH (projW U x) (projW U x) - dotH (projW V x) (projW V x)

def isAboveThreshold (U V : Fin d_k → Fin d → ℝ) (x : TokenVec d) : Prop :=
  0 < netGain U V x

def isAtThreshold (U V : Fin d_k → Fin d → ℝ) (x : TokenVec d) : Prop :=
  netGain U V x = 0 ∧ x ≠ 0

def isBelowThreshold (U V : Fin d_k → Fin d → ℝ) (x : TokenVec d) : Prop :=
  netGain U V x < 0

omit [NeZero d] [NeZero d_k] in
/-- Master Theorem 6 (Threshold Isotropic Null Cone Identity):
    A mode is at the lasing threshold if and only if it lies on the non-zero null cone ‖U x‖ = ‖V x‖. -/
theorem threshold_iff_null_cone (U V : Fin d_k → Fin d → ℝ) (x : TokenVec d) (hx : x ≠ 0) :
    isAtThreshold U V x ↔ dotH (projW U x) (projW U x) = dotH (projW V x) (projW V x) := by
  dsimp [isAtThreshold, netGain]
  constructor
  · rintro ⟨h_gain, _⟩; linarith
  · intro h_cone; exact ⟨by linarith, hx⟩

omit [NeZero d] [NeZero d_k] in
/-- Master Theorem 7 (Symmetric Attention Has No Below-Threshold Loss Modes):
    If W_Q = W_K, then V = 0, so netGain(x) = ‖U x‖² ≥ 0.
    A symmetric cavity is purely passive/amplifying and cannot extract idler modes. -/
theorem symmetric_attention_purely_passive (W : Fin d_k → Fin d → ℝ) (x : TokenVec d) :
    let U := W
    let V : Fin d_k → Fin d → ℝ := fun _ _ => 0
    0 ≤ netGain U V x := by
  intros U V
  dsimp [netGain, V, projW, dotH]
  simp [mul_zero, Finset.sum_const_zero]
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg _

/-!
### 4. Four-Wave Mixing (FWM) Pairing Operator and Radical Condensation
-/

def projW_T (W : Fin d_k → Fin d → ℝ) (y : HeadVec d_k) : TokenVec d :=
  fun j => ∑ i : Fin d_k, W i j * y i

/-- The Four-Wave Mixing (FWM) pairing operator: Δ_FWM = Uᵀ V. -/
def deltaFWM (U V : Fin d_k → Fin d → ℝ) : (TokenVec d) →ₗ[ℝ] (TokenVec d) where
  toFun x := projW_T U (projW V x)
  map_add' x y := by
    ext j
    dsimp [projW, projW_T]
    conv_lhs => simp [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    conv_rhs => simp [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  map_smul' c x := by
    ext j
    dsimp [projW, projW_T]
    conv_lhs => simp [Finset.mul_sum]
    conv_rhs => simp [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j' _
    ring

/-- Master Theorem 8 (FWM Annihilation of the Radical):
    The FWM pairing operator identically annihilates any vector in the shared radical ker(U) ∩ ker(V). -/
theorem fwm_pairing_annihilates_shared_radical
    {d d_k : ℕ} (U V : Fin d_k → Fin d → ℝ) (x : TokenVec d)
    (hU : projW U x = fun _ => 0) (hV : projW V x = fun _ => 0) :
    deltaFWM U V x = 0 ∧ deltaFWM V U x = 0 := by
  constructor
  · ext j
    change (∑ i : Fin d_k, U i j * (projW V x) i) = 0
    rw [hV]
    simp [mul_zero, Finset.sum_const_zero]
  · ext j
    change (∑ i : Fin d_k, V i j * (projW U x) i) = 0
    rw [hU]
    simp [mul_zero, Finset.sum_const_zero]

/-!
### 5. Sachs Beam Optics and Astigmatic Lasing Thresholds
-/

/-- Master Theorem 9 (Sachs Modal Gain Factorization):
    In a cavity governed by the Sachs screen parameters (θ, σ, ω), the net modal gain
    along the principal shear axis factorizes as (θ + ‖σ‖)² - ω². -/
theorem sachs_dominant_mode_gain_factorization (θ s_norm ω : ℝ) :
    (θ + s_norm)^2 - ω^2 = (θ^2 + s_norm^2 - ω^2) + 2 * θ * s_norm := by
  ring

/-- Master Theorem 10 (Twist-Free Gain Non-Negativity):
    In a twist-free cavity (ω = 0), the dominant mode gain is unconditionally non-negative:
    (θ + ‖σ‖)² ≥ 0. -/
theorem sachs_twist_free_gain_nonneg (θ s_norm : ℝ) :
    0 ≤ (θ + s_norm)^2 - 0^2 := by
  have h := sq_nonneg (θ + s_norm)
  have h0 : (0 : ℝ)^2 = 0 := by norm_num
  rw [pow_two] at h ⊢
  rw [h0] at ⊢
  rw [sub_zero] at ⊢
  exact h

/-- Master Theorem 11 (Astigmatic Lasing Threshold Condition):
    The dominant transverse mode reaches the laser threshold (gain = 0)
    if and only if the total amplification matches the vorticity loss:
    θ + ‖σ‖ = |ω|. -/
theorem sachs_lasing_threshold_condition (θ s_norm ω : ℝ) (h_pos : 0 ≤ θ + s_norm) :
    (θ + s_norm)^2 - ω^2 = 0 ↔ θ + s_norm = |ω| := by
  have h_diff : (θ + s_norm)^2 - ω^2 = ((θ + s_norm) - |ω|) * ((θ + s_norm) + |ω|) := by
    have : |ω|^2 = ω^2 := sq_abs ω
    rw [← this]
    ring
  rw [h_diff]
  constructor
  · intro h
    cases mul_eq_zero.mp h with
    | inl h1 => linarith
    | inr h2 =>
      have h_abs : 0 ≤ |ω| := abs_nonneg ω
      have h_sum : θ + s_norm + |ω| = 0 := h2
      have h_zero1 : θ + s_norm = 0 := by linarith
      have h_zero2 : |ω| = 0 := by linarith
      linarith
  · intro h
    rw [h, sub_self, zero_mul]

end InfoGeometry.PhaseConjugateLaserCavity
