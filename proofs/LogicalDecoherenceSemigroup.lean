import Mathlib
import proofs.CuntzLogicalHodgeLaplacian
import proofs.LogicalWheelerDeWittHamiltonian

noncomputable section

open Matrix
open scoped NNReal Topology

namespace LogicalDecoherenceSemigroup

abbrev LogicalMatrix :=
  Matrix (Fin 2) (Fin 2) ℂ

def logicalGamma : LogicalMatrix :=
  !![(1 : ℂ), 0;
     0,       -1]

def logicalDiagonalPart
    (A : LogicalMatrix) : LogicalMatrix :=
  (2 : ℂ)⁻¹ •
    (A + logicalGamma * A * logicalGamma)

def logicalOffDiagonalPart
    (A : LogicalMatrix) : LogicalMatrix :=
  (2 : ℂ)⁻¹ •
    (A - logicalGamma * A * logicalGamma)

def decoherenceFactor
    (t : ℝ≥0) : ℂ :=
  (Real.exp (-4 * (t : ℝ)) : ℂ)

def logicalDecoherence
    (t : ℝ≥0)
    (A : LogicalMatrix) : LogicalMatrix :=
  logicalDiagonalPart A +
    decoherenceFactor t • logicalOffDiagonalPart A

-- 1. Projector Algebra
theorem logicalGamma_sq :
    logicalGamma * logicalGamma = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem diagonalPart_add_offDiagonalPart
    (A : LogicalMatrix) :
    logicalDiagonalPart A +
        logicalOffDiagonalPart A = A := by
  unfold logicalDiagonalPart logicalOffDiagonalPart
  rw [← smul_add]
  have h : A + logicalGamma * A * logicalGamma + (A - logicalGamma * A * logicalGamma) = (2:ℂ) • A := by
    rw [two_smul]
    exact add_add_sub_cancel _ _
  rw [h, ← mul_smul]
  have h2 : ((2:ℂ)⁻¹ * 2) = 1 := inv_mul_cancel two_ne_zero
  rw [h2, one_smul]

theorem diagonalPart_idempotent
    (A : LogicalMatrix) :
    logicalDiagonalPart
        (logicalDiagonalPart A) =
      logicalDiagonalPart A := by
  unfold logicalDiagonalPart
  rw [smul_add, mul_smul_comm, smul_mul_assoc, ← smul_add]
  have h_gam : logicalGamma * (logicalGamma * A * logicalGamma) * logicalGamma = A := by
    rw [Matrix.mul_assoc logicalGamma, ← Matrix.mul_assoc logicalGamma logicalGamma A]
    rw [logicalGamma_sq, Matrix.one_mul, Matrix.mul_assoc A, logicalGamma_sq, Matrix.mul_one]
  rw [h_gam]
  have h : A + logicalGamma * A * logicalGamma + (logicalGamma * A * logicalGamma + A) = (2:ℂ) • (A + logicalGamma * A * logicalGamma) := by
    rw [two_smul]; abel
  rw [h, ← mul_smul]
  have h2 : ((2:ℂ)⁻¹ * 2) = 1 := inv_mul_cancel two_ne_zero
  rw [h2, one_smul]

theorem offDiagonalPart_idempotent
    (A : LogicalMatrix) :
    logicalOffDiagonalPart
        (logicalOffDiagonalPart A) =
      logicalOffDiagonalPart A := by
  unfold logicalOffDiagonalPart
  rw [smul_sub, mul_smul_comm, smul_mul_assoc, ← smul_sub]
  have h_gam : logicalGamma * (logicalGamma * A * logicalGamma) * logicalGamma = A := by
    rw [Matrix.mul_assoc logicalGamma, ← Matrix.mul_assoc logicalGamma logicalGamma A]
    rw [logicalGamma_sq, Matrix.one_mul, Matrix.mul_assoc A, logicalGamma_sq, Matrix.mul_one]
  rw [h_gam]
  have h : A - logicalGamma * A * logicalGamma - (logicalGamma * A * logicalGamma - A) = (2:ℂ) • (A - logicalGamma * A * logicalGamma) := by
    rw [two_smul]; abel
  rw [h, ← mul_smul]
  have h2 : ((2:ℂ)⁻¹ * 2) = 1 := inv_mul_cancel two_ne_zero
  rw [h2, one_smul]

theorem diagonalPart_offDiagonalPart
    (A : LogicalMatrix) :
    logicalDiagonalPart
        (logicalOffDiagonalPart A) = 0 := by
  unfold logicalDiagonalPart logicalOffDiagonalPart
  rw [smul_sub, mul_smul_comm, smul_mul_assoc, ← smul_add, ← smul_smul]
  have h_gam : logicalGamma * (logicalGamma * A * logicalGamma) * logicalGamma = A := by
    rw [Matrix.mul_assoc logicalGamma, ← Matrix.mul_assoc logicalGamma logicalGamma A]
    rw [logicalGamma_sq, Matrix.one_mul, Matrix.mul_assoc A, logicalGamma_sq, Matrix.mul_one]
  rw [h_gam]
  have h : A - logicalGamma * A * logicalGamma + (logicalGamma * A * logicalGamma - A) = 0 := by abel
  rw [h, smul_zero]

theorem offDiagonalPart_diagonalPart
    (A : LogicalMatrix) :
    logicalOffDiagonalPart
        (logicalDiagonalPart A) = 0 := by
  unfold logicalDiagonalPart logicalOffDiagonalPart
  rw [smul_add, mul_smul_comm, smul_mul_assoc, ← smul_sub, ← smul_smul]
  have h_gam : logicalGamma * (logicalGamma * A * logicalGamma) * logicalGamma = A := by
    rw [Matrix.mul_assoc logicalGamma, ← Matrix.mul_assoc logicalGamma logicalGamma A]
    rw [logicalGamma_sq, Matrix.one_mul, Matrix.mul_assoc A, logicalGamma_sq, Matrix.mul_one]
  rw [h_gam]
  have h : A + logicalGamma * A * logicalGamma - (logicalGamma * A * logicalGamma + A) = 0 := by abel
  rw [h, smul_zero]

-- 2. Semigroup Property
@[simp]
theorem decoherenceFactor_zero :
    decoherenceFactor 0 = 1 := by
  simp [decoherenceFactor]

theorem decoherenceFactor_add
    (t s : ℝ≥0) :
    decoherenceFactor (t + s) =
      decoherenceFactor t *
        decoherenceFactor s := by
  push_cast
  unfold decoherenceFactor
  rw [mul_add, Real.exp_add, Complex.ofReal_mul]

lemma diagonalPart_add (A B : LogicalMatrix) :
    logicalDiagonalPart (A + B) = logicalDiagonalPart A + logicalDiagonalPart B := by
  unfold logicalDiagonalPart
  rw [Matrix.mul_add, Matrix.add_mul, add_add_add_comm, smul_add]

lemma diagonalPart_smul (c : ℂ) (A : LogicalMatrix) :
    logicalDiagonalPart (c • A) = c • logicalDiagonalPart A := by
  unfold logicalDiagonalPart
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_comm]

lemma offDiagonalPart_add (A B : LogicalMatrix) :
    logicalOffDiagonalPart (A + B) = logicalOffDiagonalPart A + logicalOffDiagonalPart B := by
  unfold logicalOffDiagonalPart
  rw [Matrix.mul_add, Matrix.add_mul]
  have h : A + B - (logicalGamma * A * logicalGamma + logicalGamma * B * logicalGamma) = A - logicalGamma * A * logicalGamma + (B - logicalGamma * B * logicalGamma) := by abel
  rw [h, smul_add]

lemma offDiagonalPart_smul (c : ℂ) (A : LogicalMatrix) :
    logicalOffDiagonalPart (c • A) = c • logicalOffDiagonalPart A := by
  unfold logicalOffDiagonalPart
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_comm]

@[simp]
theorem logicalDecoherence_zero
    (A : LogicalMatrix) :
    logicalDecoherence 0 A = A := by
  simp [logicalDecoherence,
    diagonalPart_add_offDiagonalPart]

theorem logicalDecoherence_add
    (t s : ℝ≥0)
    (A : LogicalMatrix) :
    logicalDecoherence (t + s) A =
      logicalDecoherence t
        (logicalDecoherence s A) := by
  unfold logicalDecoherence
  rw [decoherenceFactor_add]
  have h_diag : logicalDiagonalPart (logicalDiagonalPart A + decoherenceFactor s • logicalOffDiagonalPart A) = logicalDiagonalPart A := by
    rw [diagonalPart_add, diagonalPart_idempotent, diagonalPart_smul, diagonalPart_offDiagonalPart, smul_zero, add_zero]
  have h_off : logicalOffDiagonalPart (logicalDiagonalPart A + decoherenceFactor s • logicalOffDiagonalPart A) = decoherenceFactor s • logicalOffDiagonalPart A := by
    rw [offDiagonalPart_add, offDiagonalPart_diagonalPart, offDiagonalPart_smul, offDiagonalPart_idempotent, zero_add]
  rw [h_diag, h_off, ← mul_smul]

-- 3. Matrix Units Action
def logicalE (a b : Fin 2) : LogicalMatrix :=
  Matrix.stdBasisMatrix a b (1 : ℂ)

lemma logicalGamma_mul_E00 :
    logicalGamma * logicalE 0 0 * logicalGamma = logicalE 0 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma logicalGamma_mul_E11 :
    logicalGamma * logicalE 1 1 * logicalGamma = logicalE 1 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma logicalGamma_mul_E01 :
    logicalGamma * logicalE 0 1 * logicalGamma = -logicalE 0 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma logicalGamma_mul_E10 :
    logicalGamma * logicalE 1 0 * logicalGamma = -logicalE 1 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem logicalDecoherence_E00
    (t : ℝ≥0) :
    logicalDecoherence t (logicalE 0 0) =
      logicalE 0 0 := by
  unfold logicalDecoherence logicalDiagonalPart logicalOffDiagonalPart
  rw [logicalGamma_mul_E00]
  have hd : logicalE 0 0 + logicalE 0 0 = (2:ℂ) • logicalE 0 0 := by rw [two_smul]
  have ho : logicalE 0 0 - logicalE 0 0 = 0 := sub_self _
  rw [hd, ho, smul_zero, smul_zero, add_zero, ← mul_smul, inv_mul_cancel two_ne_zero, one_smul]

theorem logicalDecoherence_E11
    (t : ℝ≥0) :
    logicalDecoherence t (logicalE 1 1) =
      logicalE 1 1 := by
  unfold logicalDecoherence logicalDiagonalPart logicalOffDiagonalPart
  rw [logicalGamma_mul_E11]
  have hd : logicalE 1 1 + logicalE 1 1 = (2:ℂ) • logicalE 1 1 := by rw [two_smul]
  have ho : logicalE 1 1 - logicalE 1 1 = 0 := sub_self _
  rw [hd, ho, smul_zero, smul_zero, add_zero, ← mul_smul, inv_mul_cancel two_ne_zero, one_smul]

theorem logicalDecoherence_E01
    (t : ℝ≥0) :
    logicalDecoherence t (logicalE 0 1) =
      decoherenceFactor t • logicalE 0 1 := by
  unfold logicalDecoherence logicalDiagonalPart logicalOffDiagonalPart
  rw [logicalGamma_mul_E01]
  have hd : logicalE 0 1 + -logicalE 0 1 = 0 := add_neg_cancel _
  have ho : logicalE 0 1 - -logicalE 0 1 = (2:ℂ) • logicalE 0 1 := by rw [sub_neg_eq_add, two_smul]
  rw [hd, ho, smul_zero, zero_add, ← mul_smul, inv_mul_cancel two_ne_zero, one_smul]

theorem logicalDecoherence_E10
    (t : ℝ≥0) :
    logicalDecoherence t (logicalE 1 0) =
      decoherenceFactor t • logicalE 1 0 := by
  unfold logicalDecoherence logicalDiagonalPart logicalOffDiagonalPart
  rw [logicalGamma_mul_E10]
  have hd : logicalE 1 0 + -logicalE 1 0 = 0 := add_neg_cancel _
  have ho : logicalE 1 0 - -logicalE 1 0 = (2:ℂ) • logicalE 1 0 := by rw [sub_neg_eq_add, two_smul]
  rw [hd, ho, smul_zero, zero_add, ← mul_smul, inv_mul_cancel two_ne_zero, one_smul]

-- 4. Star, Unit, Trace
theorem logicalGamma_conjTranspose : logicalGammaᴴ = logicalGamma := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem logicalDecoherence_conjTranspose
    (t : ℝ≥0)
    (A : LogicalMatrix) :
    logicalDecoherence t Aᴴ =
      (logicalDecoherence t A)ᴴ := by
  unfold logicalDecoherence logicalDiagonalPart logicalOffDiagonalPart
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_smul]
  rw [conjTranspose_add, conjTranspose_sub]
  have h_gam_mul : (logicalGamma * A * logicalGamma)ᴴ = logicalGamma * Aᴴ * logicalGamma := by
    rw [conjTranspose_mul, conjTranspose_mul, logicalGamma_conjTranspose, Matrix.mul_assoc]
  rw [h_gam_mul]
  have hs2 : star ((2:ℂ)⁻¹) = (2:ℂ)⁻¹ := by simp
  have ht : star (decoherenceFactor t) = decoherenceFactor t := by
    unfold decoherenceFactor; simp
  rw [hs2, ht]

theorem logicalDecoherence_one
    (t : ℝ≥0) :
    logicalDecoherence t (1 : LogicalMatrix) = 1 := by
  unfold logicalDecoherence logicalDiagonalPart logicalOffDiagonalPart
  have h : logicalGamma * 1 * logicalGamma = 1 := by
    rw [Matrix.mul_one, logicalGamma_sq]
  rw [h]
  have hd : (1:LogicalMatrix) + 1 = (2:ℂ) • 1 := by rw [two_smul]
  have ho : (1:LogicalMatrix) - 1 = 0 := sub_self _
  rw [hd, ho, smul_zero, smul_zero, add_zero, ← mul_smul, inv_mul_cancel two_ne_zero, one_smul]

theorem logicalDecoherence_trace
    (t : ℝ≥0)
    (A : LogicalMatrix) :
    Matrix.trace (logicalDecoherence t A) =
      Matrix.trace A := by
  unfold logicalDecoherence logicalDiagonalPart logicalOffDiagonalPart
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub]
  have ht : Matrix.trace (logicalGamma * A * logicalGamma) = Matrix.trace A := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, logicalGamma_sq, Matrix.mul_one]
  rw [ht]
  have hd : Matrix.trace A + Matrix.trace A = (2:ℂ) * Matrix.trace A := by ring
  have ho : Matrix.trace A - Matrix.trace A = 0 := sub_self _
  rw [hd, ho, mul_zero, add_zero, ← mul_assoc, inv_mul_cancel two_ne_zero, one_mul]

-- 5. CPTP Layer
def qt (t : ℝ≥0) : ℝ := Real.exp (-4 * (t : ℝ))
def at_ (t : ℝ≥0) : ℝ := (1 + qt t) / 2
def bt_ (t : ℝ≥0) : ℝ := (1 - qt t) / 2

def K0 (t : ℝ≥0) : LogicalMatrix := (Real.sqrt (at_ t) : ℂ) • 1
def K1 (t : ℝ≥0) : LogicalMatrix := (Real.sqrt (bt_ t) : ℂ) • logicalGamma

lemma qt_bounds (t : ℝ≥0) : 0 < qt t ∧ qt t ≤ 1 := by
  unfold qt
  have h1 : 0 < Real.exp (-4 * (t : ℝ)) := Real.exp_pos _
  have h2 : Real.exp (-4 * (t : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ (t : ℝ) := t.property
    linarith
  exact ⟨h1, h2⟩

lemma at_nonneg (t : ℝ≥0) : 0 ≤ at_ t := by
  have := qt_bounds t
  unfold at_
  linarith

lemma bt_nonneg (t : ℝ≥0) : 0 ≤ bt_ t := by
  have := qt_bounds t
  unfold bt_
  linarith

lemma at_add_bt (t : ℝ≥0) : at_ t + bt_ t = 1 := by
  unfold at_ bt_
  ring

theorem logicalDecoherence_kraus_form
    (t : ℝ≥0) (A : LogicalMatrix) :
    logicalDecoherence t A =
      K0 t * A * (K0 t)ᴴ + K1 t * A * (K1 t)ᴴ := by
  unfold logicalDecoherence logicalDiagonalPart logicalOffDiagonalPart
  unfold K0 K1
  rw [conjTranspose_smul, conjTranspose_smul, conjTranspose_one, logicalGamma_conjTranspose]
  have hstar1 : star (Real.sqrt (at_ t) : ℂ) = Real.sqrt (at_ t) := by simp [Real.sqrt_nonneg]
  have hstar2 : star (Real.sqrt (bt_ t) : ℂ) = Real.sqrt (bt_ t) := by simp [Real.sqrt_nonneg]
  rw [hstar1, hstar2]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, ← smul_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_smul]
  have hs1 : ((Real.sqrt (at_ t) : ℂ) * Real.sqrt (at_ t)) = (at_ t : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (at_nonneg t)]
  have hs2 : ((Real.sqrt (bt_ t) : ℂ) * Real.sqrt (bt_ t)) = (bt_ t : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (bt_nonneg t)]
  rw [hs1, hs2]
  unfold at_ bt_
  have hd : (2:ℂ)⁻¹ • (A + logicalGamma * A * logicalGamma) = (2:ℂ)⁻¹ • A + (2:ℂ)⁻¹ • (logicalGamma * A * logicalGamma) := smul_add _ _ _
  have ho : decoherenceFactor t • ((2:ℂ)⁻¹ • (A - logicalGamma * A * logicalGamma)) = (decoherenceFactor t * (2:ℂ)⁻¹) • A - (decoherenceFactor t * (2:ℂ)⁻¹) • (logicalGamma * A * logicalGamma) := by
    rw [smul_sub, mul_smul]
  rw [hd, ho]
  have ha1 : (((1 + qt t) / 2 : ℝ) : ℂ) = (2:ℂ)⁻¹ + (qt t : ℂ) * (2:ℂ)⁻¹ := by
    push_cast; ring
  have ha2 : (((1 - qt t) / 2 : ℝ) : ℂ) = (2:ℂ)⁻¹ - (qt t : ℂ) * (2:ℂ)⁻¹ := by
    push_cast; ring
  rw [ha1, ha2]
  have hdf : decoherenceFactor t = (qt t : ℂ) := rfl
  rw [hdf]
  rw [add_smul, sub_smul]
  abel

theorem logicalDecoherence_kraus_complete
    (t : ℝ≥0) :
    (K0 t)ᴴ * K0 t + (K1 t)ᴴ * K1 t = 1 := by
  unfold K0 K1
  rw [conjTranspose_smul, conjTranspose_smul, conjTranspose_one, logicalGamma_conjTranspose]
  have hstar1 : star (Real.sqrt (at_ t) : ℂ) = Real.sqrt (at_ t) := by simp [Real.sqrt_nonneg]
  have hstar2 : star (Real.sqrt (bt_ t) : ℂ) = Real.sqrt (bt_ t) := by simp [Real.sqrt_nonneg]
  rw [hstar1, hstar2]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, ← smul_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul, logicalGamma_sq, ← smul_smul]
  have hs1 : ((Real.sqrt (at_ t) : ℂ) * Real.sqrt (at_ t)) = (at_ t : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (at_nonneg t)]
  have hs2 : ((Real.sqrt (bt_ t) : ℂ) * Real.sqrt (bt_ t)) = (bt_ t : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (bt_nonneg t)]
  rw [hs1, hs2, ← add_smul, ← Complex.ofReal_add, at_add_bt t]
  simp

-- 6. Asymptotic Decoherence
theorem logicalDecoherence_tendsto
    (A : LogicalMatrix) :
    Filter.Tendsto
      (fun t : ℝ≥0 =>
        logicalDecoherence t A)
      Filter.atTop
      (nhds (logicalDiagonalPart A)) := by
  -- decoherenceFactor t -> 0 as t -> ∞
  have h1 : Filter.Tendsto (fun t : ℝ≥0 => (-4 * (t : ℝ))) Filter.atTop Filter.atBot := by
    apply Filter.Tendsto.atBot_mul_const (by norm_num)
    exact Filter.tendsto_coe_nnreal_atTop
  have h2 : Filter.Tendsto (fun t : ℝ≥0 => Real.exp (-4 * (t : ℝ))) Filter.atTop (nhds 0) :=
    Filter.Tendsto.comp Real.tendsto_exp_atBot h1
  have h3 : Filter.Tendsto (fun t : ℝ≥0 => decoherenceFactor t) Filter.atTop (nhds 0) := by
    have h_cast : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (nhds 0) (nhds 0) := complex.continuous_of_real.continuousAt
    exact Filter.Tendsto.comp h_cast h2
  have h4 : Filter.Tendsto (fun t : ℝ≥0 => decoherenceFactor t • logicalOffDiagonalPart A) Filter.atTop (nhds 0) := by
    have h_zero : (0 : ℂ) • logicalOffDiagonalPart A = 0 := zero_smul _ _
    rw [← h_zero]
    exact Filter.Tendsto.smul_const h3 _
  have h5 : Filter.Tendsto (fun t : ℝ≥0 => logicalDiagonalPart A + decoherenceFactor t • logicalOffDiagonalPart A) Filter.atTop (nhds (logicalDiagonalPart A + 0)) :=
    Filter.Tendsto.const_add (logicalDiagonalPart A) h4
  rw [add_zero] at h5
  exact h5

-- 7. Transport to Cuntz logical corner
variable {A_alg : Type*} [Ring A_alg] [StarRing A_alg] [Algebra ℂ A_alg] [StarModule ℂ A_alg]
variable (S : Fin 2 → A_alg) [hC : CuntzWordSpaceQEC.CuntzO2 (S 0) (S 1)]

def IsLogicallySupported (a : A_alg) : Prop :=
  CuntzPeirceLogicalCorner.logicalCodeUnit S * a = a ∧ a * CuntzPeirceLogicalCorner.logicalCodeUnit S = a

def logicalGrading : A_alg :=
  CuntzPeirceLogicalCorner.cuntzLogicalMatrixUnit S 0 0 - CuntzPeirceLogicalCorner.cuntzLogicalMatrixUnit S 1 1

theorem logicalGrading_sq_Cuntz :
    logicalGrading S * logicalGrading S = CuntzPeirceLogicalCorner.logicalCodeUnit S :=
  logicalSigmaZ_sq S

def logicalDiagonalPartOnCorner (a : A_alg) : A_alg :=
  ((2 : ℂ)⁻¹) • (a + logicalGrading S * a * logicalGrading S)

def logicalOffDiagonalPartOnCorner (a : A_alg) : A_alg :=
  ((2 : ℂ)⁻¹) • (a - logicalGrading S * a * logicalGrading S)

def logicalDecoherenceOnCorner (t : ℝ≥0) (a : A_alg) : A_alg :=
  logicalDiagonalPartOnCorner S a + decoherenceFactor t • logicalOffDiagonalPartOnCorner S a

-- 8. WDW Hamiltonian deformation
lemma logicalGrading_eq_sigmaZ : logicalGrading S = logicalSigmaZ S := rfl

theorem logicalDecoherence_WDWHamiltonian
    (τ : ℝ≥0)
    (t x y : ℝ) :
    logicalDecoherenceOnCorner S τ
        (logicalWDWHamiltonian S t x y) =
      logicalWDWHamiltonian S
        t x
        (Real.exp (-4 * (τ : ℝ)) * y) := by
  unfold logicalDecoherenceOnCorner logicalDiagonalPartOnCorner logicalOffDiagonalPartOnCorner
  unfold logicalWDWHamiltonian
  rw [logicalGrading_eq_sigmaZ]
  have h_Z : logicalSigmaZ S * ((t : ℂ) • CuntzPeirceLogicalCorner.logicalCodeUnit S + (x : ℂ) • logicalSigmaZ S + (y : ℂ) • logicalSigmaX S) * logicalSigmaZ S = (t : ℂ) • CuntzPeirceLogicalCorner.logicalCodeUnit S + (x : ℂ) • logicalSigmaZ S - (y : ℂ) • logicalSigmaX S := by
    rw [mul_add, add_mul, mul_add, add_mul]
    rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm]
    rw [logicalSigmaZ_mul_logicalCodeUnit S, logicalCodeUnit_mul_logicalSigmaZ S]
    rw [logicalSigmaZ_sq S]
    have h_anti : logicalSigmaZ S * logicalSigmaX S * logicalSigmaZ S = - logicalSigmaX S := by
      have h_anti1 := logicalSigmaZ_anticommute_logicalSigmaX S
      have h_anti2 : logicalSigmaZ S * logicalSigmaX S = - (logicalSigmaX S * logicalSigmaZ S) := eq_neg_iff_add_eq_zero.mpr h_anti1
      rw [h_anti2, neg_mul, ← mul_assoc, logicalSigmaZ_sq S, logicalSigmaX_mul_logicalCodeUnit S]
    rw [h_anti, smul_neg, sub_eq_add_neg]
  rw [h_Z]
  have h_add : ((t : ℂ) • CuntzPeirceLogicalCorner.logicalCodeUnit S + (x : ℂ) • logicalSigmaZ S + (y : ℂ) • logicalSigmaX S) + ((t : ℂ) • CuntzPeirceLogicalCorner.logicalCodeUnit S + (x : ℂ) • logicalSigmaZ S - (y : ℂ) • logicalSigmaX S) = (2 : ℂ) • ((t : ℂ) • CuntzPeirceLogicalCorner.logicalCodeUnit S + (x : ℂ) • logicalSigmaZ S) := by
    rw [two_smul]
    abel
  have h_sub : ((t : ℂ) • CuntzPeirceLogicalCorner.logicalCodeUnit S + (x : ℂ) • logicalSigmaZ S + (y : ℂ) • logicalSigmaX S) - ((t : ℂ) • CuntzPeirceLogicalCorner.logicalCodeUnit S + (x : ℂ) • logicalSigmaZ S - (y : ℂ) • logicalSigmaX S) = (2 : ℂ) • ((y : ℂ) • logicalSigmaX S) := by
    rw [two_smul]
    abel
  rw [h_add, h_sub]
  rw [← mul_smul, ← mul_smul, inv_mul_cancel two_ne_zero, one_smul, one_smul]
  unfold decoherenceFactor
  rw [smul_smul, mul_comm]
  have h_coe : (y : ℂ) * (Real.exp (-4 * (τ : ℝ)) : ℂ) = ((Real.exp (-4 * (τ : ℝ)) * y : ℝ) : ℂ) := by
    push_cast; ring
  rw [h_coe]
  abel

end LogicalDecoherenceSemigroup
