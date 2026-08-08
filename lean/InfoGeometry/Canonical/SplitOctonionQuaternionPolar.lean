import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.Exponential
import InfoGeometry.Canonical.SplitOctonionQuaternionChart
import InfoGeometry.Canonical.SplitOctonionExpLog

noncomputable section

namespace SplitOctonion

open scoped Quaternion
@[simp] lemma H_smul_mul_smul (r s : ℝ) (x y : H) : (r • x) * (s • y) = (r * s) • (x * y) := by
  ext <;> simp <;> ring

@[simp] lemma H_smul_zero (r : ℝ) : r • (0 : H) = 0 := by
  ext <;> simp

@[simp] lemma H_star_mul_self (g : H) : star g * g = (Quaternion.normSq g : ℝ) • (1 : H) := by
  ext <;> simp [Quaternion.normSq] <;> ring

@[simp] lemma add_a (X Y : SplitOctonion) : (X + Y).a = X.a + Y.a := rfl
@[simp] lemma add_b (X Y : SplitOctonion) : (X + Y).b = X.b + Y.b := rfl
@[simp] lemma sub_a (X Y : SplitOctonion) : (X - Y).a = X.a - Y.a := rfl
@[simp] lemma sub_b (X Y : SplitOctonion) : (X - Y).b = X.b - Y.b := rfl
@[simp] lemma neg_a (X : SplitOctonion) : (-X).a = -X.a := rfl
@[simp] lemma neg_b (X : SplitOctonion) : (-X).b = -X.b := rfl
@[simp] lemma smul_a (r : ℝ) (X : SplitOctonion) : (r • X).a = r • X.a := rfl
@[simp] lemma smul_b (r : ℝ) (X : SplitOctonion) : (r • X).b = r • X.b := rfl
@[simp] lemma one_a : (1 : SplitOctonion).a = 1 := rfl
@[simp] lemma one_b : (1 : SplitOctonion).b = 0 := rfl
@[simp] lemma zero_a : (0 : SplitOctonion).a = 0 := rfl
@[simp] lemma zero_b : (0 : SplitOctonion).b = 0 := rfl

@[simp] lemma mul_a_of_b_zero (A C D : H) : (⟨A, 0⟩ * ⟨C, D⟩ : SplitOctonion).a = A * C := by
  change A * C + star D * 0 = A * C
  rw [mul_zero, add_zero]

@[simp] lemma mul_b_of_b_zero (A C D : H) : (⟨A, 0⟩ * ⟨C, D⟩ : SplitOctonion).b = D * A := by
  change D * A + 0 * star C = D * A
  rw [zero_mul, add_zero]

/-- If a split octonion has positive norm, it admits a polar decomposition. -/
def isHyperbolic (X : SplitOctonion) : Prop :=
  normSQ X > 0

theorem a_ne_zero_of_isHyperbolic (X : SplitOctonion) (h : isHyperbolic X) : X.a ≠ 0 := by
  intro h_zero
  unfold isHyperbolic normSQ at h
  have h1 : (X.a * star X.a).re = Quaternion.normSq X.a := (normSq_eq_re_mul_star X.a).symm
  have h2 : (X.b * star X.b).re = Quaternion.normSq X.b := (normSq_eq_re_mul_star X.b).symm
  rw [h1, h2] at h
  rw [h_zero, map_zero] at h
  have h_b_nonneg : 0 ≤ Quaternion.normSq X.b := Quaternion.normSq_nonneg
  linarith

/-- The radial coordinate ρ = √(N(X)). -/
def polarRho (X : SplitOctonion) (_h : isHyperbolic X) : ℝ :=
  Real.sqrt (normSQ X)

/-- The rapidity coordinate η, where cosh(η) = √(N(X.a)) / ρ. -/
def polarEta (X : SplitOctonion) (h : isHyperbolic X) : ℝ :=
  let x := Real.sqrt (Quaternion.normSq X.a) / polarRho X h
  Real.arcosh x

/-- The unit quaternion u = X.a / √(N(X.a)). -/
def polarU (X : SplitOctonion) (_ha : X.a ≠ 0) : H :=
  (Real.sqrt (Quaternion.normSq X.a))⁻¹ • X.a

/-- The unit quaternion v = X.b / √(N(X.b)). -/
def polarV (X : SplitOctonion) (_hb : X.b ≠ 0) : H :=
  (Real.sqrt (Quaternion.normSq X.b))⁻¹ • X.b

/-- The generator g = v * u⁻¹. -/
def polarG (X : SplitOctonion) (ha : X.a ≠ 0) (hb : X.b ≠ 0) : H :=
  polarV X hb * (polarU X ha)⁻¹

@[simp] theorem polarU_normSq (X : SplitOctonion) (ha : X.a ≠ 0) :
    Quaternion.normSq (polarU X ha) = 1 := by
  unfold polarU
  rw [Quaternion.normSq_smul]
  have h_pos : 0 ≤ Quaternion.normSq X.a := Quaternion.normSq_nonneg
  have h_ne : Quaternion.normSq X.a ≠ 0 := mt Quaternion.normSq_eq_zero.mp ha
  have h_sq : (Real.sqrt (Quaternion.normSq X.a)) ^ 2 = Quaternion.normSq X.a := Real.sq_sqrt h_pos
  calc ((Real.sqrt (Quaternion.normSq X.a))⁻¹) ^ 2 * Quaternion.normSq X.a
    _ = (Real.sqrt (Quaternion.normSq X.a))⁻¹ ^ 2 * (Real.sqrt (Quaternion.normSq X.a)) ^ 2 := by rw [h_sq]
    _ = ((Real.sqrt (Quaternion.normSq X.a))⁻¹ * Real.sqrt (Quaternion.normSq X.a)) ^ 2 := by rw [mul_pow]
    _ = 1 ^ 2 := by
      have h_zero : Real.sqrt (Quaternion.normSq X.a) ≠ 0 := by
        intro h
        have h2 : (Real.sqrt (Quaternion.normSq X.a)) ^ 2 = 0 ^ 2 := by rw [h]
        rw [h_sq] at h2
        have h3 : 0 ^ 2 = (0 : ℝ) := by norm_num
        rw [h3] at h2
        exact h_ne h2
      rw [inv_mul_cancel₀ h_zero]
    _ = 1 := one_pow 2

@[simp] theorem polarV_normSq (X : SplitOctonion) (hb : X.b ≠ 0) :
    Quaternion.normSq (polarV X hb) = 1 := by
  unfold polarV
  rw [Quaternion.normSq_smul]
  have h_pos : 0 ≤ Quaternion.normSq X.b := Quaternion.normSq_nonneg
  have h_ne : Quaternion.normSq X.b ≠ 0 := mt Quaternion.normSq_eq_zero.mp hb
  have h_sq : (Real.sqrt (Quaternion.normSq X.b)) ^ 2 = Quaternion.normSq X.b := Real.sq_sqrt h_pos
  calc ((Real.sqrt (Quaternion.normSq X.b))⁻¹) ^ 2 * Quaternion.normSq X.b
    _ = (Real.sqrt (Quaternion.normSq X.b))⁻¹ ^ 2 * (Real.sqrt (Quaternion.normSq X.b)) ^ 2 := by rw [h_sq]
    _ = ((Real.sqrt (Quaternion.normSq X.b))⁻¹ * Real.sqrt (Quaternion.normSq X.b)) ^ 2 := by rw [mul_pow]
    _ = 1 ^ 2 := by
      have h_zero : Real.sqrt (Quaternion.normSq X.b) ≠ 0 := by
        intro h
        have h2 : (Real.sqrt (Quaternion.normSq X.b)) ^ 2 = 0 ^ 2 := by rw [h]
        rw [h_sq] at h2
        have h3 : 0 ^ 2 = (0 : ℝ) := by norm_num
        rw [h3] at h2
        exact h_ne h2
      rw [inv_mul_cancel₀ h_zero]
    _ = 1 := one_pow 2

@[simp] theorem polarG_normSq (X : SplitOctonion) (ha : X.a ≠ 0) (hb : X.b ≠ 0) :
    Quaternion.normSq (polarG X ha hb) = 1 := by
  unfold polarG
  rw [map_mul Quaternion.normSq, Quaternion.normSq_inv, polarV_normSq X hb, polarU_normSq X ha, inv_one, mul_one]

/-- J_g is the pure imaginary octonion element (0, g). -/
def J_g (g : H) : SplitOctonion :=
  ⟨0, g⟩

lemma expHyperbolic_J_g (eta : ℝ) (g : H) :
    expHyperbolic 1 eta (J_g g) = ⟨Real.cosh eta • (1 : H), Real.sinh eta • g⟩ := by
  unfold expHyperbolic J_g
  apply SplitOctonion.ext
  · change (1 * Real.cosh eta) • (1 : H) + (1 * Real.sinh eta) • (0 : H) = Real.cosh eta • 1
    rw [one_mul, H_smul_zero, add_zero]
  · change (0 : H) + (1 * Real.sinh eta) • g = Real.sinh eta • g
    rw [one_mul, zero_add]

lemma cosh_polarEta (X : SplitOctonion) (h : isHyperbolic X) :
    Real.cosh (polarEta X h) = Real.sqrt (Quaternion.normSq X.a) / polarRho X h := by
  unfold polarEta
  apply Real.cosh_arcosh
  have h1 : 0 ≤ Quaternion.normSq X.a := Quaternion.normSq_nonneg
  have h2 : 0 ≤ Quaternion.normSq X.b := Quaternion.normSq_nonneg
  have h3 : 0 ≤ normSQ X := le_of_lt h
  have h4 : normSQ X ≤ Quaternion.normSq X.a := by
    unfold normSQ
    have h1a : (X.a * star X.a).re = Quaternion.normSq X.a := (normSq_eq_re_mul_star X.a).symm
    have h2b : (X.b * star X.b).re = Quaternion.normSq X.b := (normSq_eq_re_mul_star X.b).symm
    rw [h1a, h2b]
    linarith
  have h5 : polarRho X h = Real.sqrt (normSQ X) := rfl
  rw [h5]
  apply (one_le_div (Real.sqrt_pos.mpr h)).mpr
  apply Real.sqrt_le_sqrt
  exact h4

lemma sinh_polarEta (X : SplitOctonion) (h : isHyperbolic X) :
    Real.sinh (polarEta X h) = Real.sqrt (Quaternion.normSq X.b) / polarRho X h := by
  unfold polarEta
  have h1 : 0 ≤ Quaternion.normSq X.a := Quaternion.normSq_nonneg
  have h2 : 0 ≤ Quaternion.normSq X.b := Quaternion.normSq_nonneg
  have h3 : 0 ≤ normSQ X := le_of_lt h
  have h1a : (X.a * star X.a).re = Quaternion.normSq X.a := (normSq_eq_re_mul_star X.a).symm
  have h2b : (X.b * star X.b).re = Quaternion.normSq X.b := (normSq_eq_re_mul_star X.b).symm
  have h4 : normSQ X ≤ Quaternion.normSq X.a := by
    unfold normSQ
    rw [h1a, h2b]
    linarith
  have h5 : polarRho X h = Real.sqrt (normSQ X) := rfl
  have h6 : 1 ≤ Real.sqrt (Quaternion.normSq X.a) / polarRho X h := by
    rw [h5]
    apply (one_le_div (Real.sqrt_pos.mpr h)).mpr
    apply Real.sqrt_le_sqrt
    exact h4
  rw [Real.sinh_arcosh h6]
  rw [h5]
  have h7 : (Real.sqrt (Quaternion.normSq X.a) / Real.sqrt (normSQ X)) ^ 2 = Quaternion.normSq X.a / normSQ X := by
    rw [div_pow, Real.sq_sqrt h1, Real.sq_sqrt h3]
  rw [h7]
  have h8 : Quaternion.normSq X.a / normSQ X - 1 = Quaternion.normSq X.b / normSQ X := by
    rw [sub_eq_iff_eq_add]
    have h_norm : normSQ X = Quaternion.normSq X.a - Quaternion.normSq X.b := by
      unfold normSQ
      rw [h1a, h2b]
    rw [div_add_one (ne_of_gt h)]
    rw [h_norm]
    ring
  rw [h8]
  rw [Real.sqrt_div h2]

/-- The polar decomposition theorem.
    $X = \rho(u, 0) e^{\eta J_g}$. -/
theorem polar_decomposition (X : SplitOctonion) (h : isHyperbolic X) (hb : X.b ≠ 0) :
    X = ⟨polarRho X h • polarU X (a_ne_zero_of_isHyperbolic X h), 0⟩ *
        expHyperbolic 1 (polarEta X h) (J_g (polarG X (a_ne_zero_of_isHyperbolic X h) hb)) := by
  have ha := a_ne_zero_of_isHyperbolic X h
  have h_cosh := cosh_polarEta X h
  have h_sinh := sinh_polarEta X h
  rw [expHyperbolic_J_g]
  apply SplitOctonion.ext
  · rw [mul_a_of_b_zero]
    rw [h_cosh]
    unfold polarU
    rw [smul_smul]
    rw [H_smul_mul_smul]
    rw [mul_one]
    have h_rho_pos : polarRho X h ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
    have h_norm_pos : Real.sqrt (Quaternion.normSq X.a) ≠ 0 := by
      have h_sq := Quaternion.normSq_ne_zero.mpr ha
      exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne Quaternion.normSq_nonneg h_sq.symm))
    have h_calc : (polarRho X h * (Real.sqrt (Quaternion.normSq X.a))⁻¹) * (Real.sqrt (Quaternion.normSq X.a) / polarRho X h) = 1 := by
      rw [div_eq_mul_inv]
      have : (polarRho X h * (Real.sqrt (Quaternion.normSq X.a))⁻¹) * (Real.sqrt (Quaternion.normSq X.a) * (polarRho X h)⁻¹)
           = (polarRho X h * (polarRho X h)⁻¹) * ((Real.sqrt (Quaternion.normSq X.a))⁻¹ * Real.sqrt (Quaternion.normSq X.a)) := by ring
      rw [this, mul_inv_cancel₀ h_rho_pos, inv_mul_cancel₀ h_norm_pos, mul_one]
    rw [h_calc, one_smul]
  · rw [mul_b_of_b_zero]
    rw [h_sinh]
    rw [H_smul_mul_smul]
    have h_rho_pos : polarRho X h ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h)
    rw [div_mul_cancel₀ _ h_rho_pos]
    unfold polarG
    rw [mul_assoc]
    have h_u_ne : polarU X ha ≠ 0 := by
      unfold polarU
      have h_norm_a_pos : Real.sqrt (Quaternion.normSq X.a) ≠ 0 := by
        have h_sq := Quaternion.normSq_ne_zero.mpr ha
        exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne Quaternion.normSq_nonneg h_sq.symm))
      exact smul_ne_zero (inv_ne_zero h_norm_a_pos) ha
    rw [inv_mul_cancel₀ h_u_ne, mul_one]
    unfold polarV
    have h_norm_b_pos : Real.sqrt (Quaternion.normSq X.b) ≠ 0 := by
      have h_sq := Quaternion.normSq_ne_zero.mpr hb
      exact ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne Quaternion.normSq_nonneg h_sq.symm))
    rw [smul_smul]
    rw [mul_inv_cancel₀ h_norm_b_pos, one_smul]

@[simp]
theorem normSq_polarU (X : SplitOctonion) (ha : X.a ≠ 0) :
    Quaternion.normSq (polarU X ha) = 1 := by
  unfold polarU
  rw [Quaternion.normSq_smul]
  have h_norm_pos : 0 < Quaternion.normSq X.a := lt_of_le_of_ne Quaternion.normSq_nonneg (Quaternion.normSq_ne_zero.mpr ha).symm
  have h_sq : (Real.sqrt (Quaternion.normSq X.a))⁻¹ ^ 2 = (Quaternion.normSq X.a)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (le_of_lt h_norm_pos)]
  rw [h_sq, inv_mul_cancel₀ (ne_of_gt h_norm_pos)]

@[simp]
theorem normSq_polarV (X : SplitOctonion) (hb : X.b ≠ 0) :
    Quaternion.normSq (polarV X hb) = 1 := by
  unfold polarV
  rw [Quaternion.normSq_smul]
  have h_norm_pos : 0 < Quaternion.normSq X.b := lt_of_le_of_ne Quaternion.normSq_nonneg (Quaternion.normSq_ne_zero.mpr hb).symm
  have h_sq : (Real.sqrt (Quaternion.normSq X.b))⁻¹ ^ 2 = (Quaternion.normSq X.b)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (le_of_lt h_norm_pos)]
  rw [h_sq, inv_mul_cancel₀ (ne_of_gt h_norm_pos)]

@[simp]
theorem normSq_polarG (X : SplitOctonion) (ha : X.a ≠ 0) (hb : X.b ≠ 0) :
    Quaternion.normSq (polarG X ha hb) = 1 := by
  unfold polarG
  rw [map_mul Quaternion.normSq, Quaternion.normSq_inv, normSq_polarV X hb, normSq_polarU X ha, inv_one, mul_one]

lemma star_mul_self_eq_normSq (g : H) : star g * g = (Quaternion.normSq g : ℝ) • (1 : H) := by
  exact H_star_mul_self g

@[simp]
theorem J_g_sq (g : H) (hg : Quaternion.normSq g = 1) :
    J_g g * J_g g = 1 := by
  unfold J_g
  apply SplitOctonion.ext
  · change 0 * 0 + star g * g = (1 : H)
    rw [H_star_mul_self, hg, one_smul, zero_mul, zero_add]
  · change g * 0 + g * star 0 = (0 : H)
    simp

@[simp]
theorem polarG_J_g_sq (X : SplitOctonion) (ha : X.a ≠ 0) (hb : X.b ≠ 0) :
    J_g (polarG X ha hb) * J_g (polarG X ha hb) = 1 :=
  J_g_sq (polarG X ha hb) (normSq_polarG X ha hb)

end SplitOctonion
