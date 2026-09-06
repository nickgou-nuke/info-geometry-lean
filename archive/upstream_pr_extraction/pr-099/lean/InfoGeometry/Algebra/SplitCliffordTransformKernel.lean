import Mathlib.Tactic
import Mathlib.Algebra.Ring.Idempotent

/-!
# Split Clifford Transform Kernels
-/

variable {A : Type*} [Ring A] [Algebra ℝ A]

class HyperbolicGenerator (H : A) : Prop where
  sq_eq_one : H ^ 2 = 1

class EllipticGenerator (J : A) : Prop where
  sq_eq_neg_one : J ^ 2 = -1

namespace SplitCliffordTransformKernel

variable (H : A)

/-- The algebra-valued hyperbolic kernel associated with a square-one generator.
This is the finite closed form of the exponential kernel; no analytic
exponential on the ambient algebra is assumed. -/
noncomputable def hyperbolicKernel (t : ℝ) : A :=
  Real.cosh t • (1 : A) + Real.sinh t • H

noncomputable def peircePlus : A :=
  (2 : ℝ)⁻¹ • (1 + H)

noncomputable def peirceMinus : A :=
  (2 : ℝ)⁻¹ • (1 - H)

lemma two_smul_one_eq_two : (2 : ℝ) • (1 : A) = 1 + 1 := by
  calc
    (2 : ℝ) • (1 : A) = (1 + 1 : ℝ) • (1 : A) := by norm_num
    _ = (1:ℝ) • (1:A) + (1:ℝ) • (1:A) := by rw [add_smul]
    _ = 1 + 1 := by simp

lemma two_smul_H_eq_two_H : (2 : ℝ) • H = H + H := by
  calc
    (2 : ℝ) • H = (1 + 1 : ℝ) • H := by norm_num
    _ = (1:ℝ) • H + (1:ℝ) • H := by rw [add_smul]
    _ = H + H := by simp

theorem peircePlus_add_peirceMinus :
    peircePlus H + peirceMinus H = 1 := by
  unfold peircePlus peirceMinus
  rw [← smul_add]
  have h : (1 : A) + H + (1 - H) = (2 : ℝ) • (1 : A) := by
    rw [two_smul_one_eq_two]
    abel
  rw [h, smul_smul]
  have h3 : (2 : ℝ)⁻¹ * 2 = 1 := inv_mul_cancel₀ (by norm_num)
  rw [h3, one_smul]

theorem peircePlus_sub_peirceMinus :
    peircePlus H - peirceMinus H = H := by
  unfold peircePlus peirceMinus
  rw [← smul_sub]
  have h : (1 : A) + H - (1 - H) = (2 : ℝ) • H := by
    rw [two_smul_H_eq_two_H]
    abel
  rw [h, smul_smul]
  have h3 : (2 : ℝ)⁻¹ * 2 = 1 := inv_mul_cancel₀ (by norm_num)
  rw [h3, one_smul]

theorem peircePlus_sq [HyperbolicGenerator H] :
    (peircePlus H) ^ 2 = peircePlus H := by
  unfold peircePlus
  rw [smul_pow]
  have h_sq : ((1:A) + H)^2 = ((2:ℝ) • (1:A)) + ((2:ℝ) • H) := by
    have H2 : H * H = 1 := by
      have h_sq := HyperbolicGenerator.sq_eq_one (H := H)
      rw [sq] at h_sq
      exact h_sq
    rw [two_smul_one_eq_two, two_smul_H_eq_two_H]
    calc
      ((1:A) + H)^2 = (1 + H) * (1 + H) := by rw [sq]
      _ = (1+1:A) + (H+H) := by
        simp only [add_mul, mul_add, one_mul, mul_one, H2]
        abel
  rw [h_sq]
  rw [← smul_add, smul_smul]
  have h4 : (2:ℝ)⁻¹^2 * 2 = (2:ℝ)⁻¹ := by
    calc
      (2:ℝ)⁻¹^2 * 2 = (2:ℝ)⁻¹ * ((2:ℝ)⁻¹ * 2) := by { rw [sq]; ring }
      _ = (2:ℝ)⁻¹ * 1 := by rw [inv_mul_cancel₀ (by norm_num)]
      _ = (2:ℝ)⁻¹ := mul_one _
  rw [h4]

theorem peirceMinus_sq [HyperbolicGenerator H] :
    (peirceMinus H) ^ 2 = peirceMinus H := by
  unfold peirceMinus
  rw [smul_pow]
  have h_sq : ((1:A) - H)^2 = ((2:ℝ) • (1:A)) - ((2:ℝ) • H) := by
    have H2 : H * H = 1 := by
      have h_sq := HyperbolicGenerator.sq_eq_one (H := H)
      rw [sq] at h_sq
      exact h_sq
    rw [two_smul_one_eq_two, two_smul_H_eq_two_H]
    calc
      ((1:A) - H)^2 = (1 - H) * (1 - H) := by rw [sq]
      _ = (1+1:A) - (H+H) := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, H2]
        abel
  rw [h_sq]
  rw [← smul_sub, smul_smul]
  have h4 : (2:ℝ)⁻¹^2 * 2 = (2:ℝ)⁻¹ := by
    calc
      (2:ℝ)⁻¹^2 * 2 = (2:ℝ)⁻¹ * ((2:ℝ)⁻¹ * 2) := by { rw [sq]; ring }
      _ = (2:ℝ)⁻¹ * 1 := by rw [inv_mul_cancel₀ (by norm_num)]
      _ = (2:ℝ)⁻¹ := mul_one _
  rw [h4]

theorem peircePlus_mul_peirceMinus [HyperbolicGenerator H] :
    peircePlus H * peirceMinus H = 0 := by
  unfold peircePlus peirceMinus
  rw [smul_mul_smul]
  have h : ((1:A) + H) * (1 - H) = 0 := by
    have H2 : H * H = 1 := by
      have h_sq := HyperbolicGenerator.sq_eq_one (H := H)
      rw [sq] at h_sq
      exact h_sq
    simp only [add_mul, sub_mul, mul_sub, mul_add, one_mul, mul_one, H2]
    abel
  rw [h, smul_zero]

theorem peirceMinus_mul_peircePlus [HyperbolicGenerator H] :
    peirceMinus H * peircePlus H = 0 := by
  unfold peircePlus peirceMinus
  rw [smul_mul_smul]
  have h : ((1:A) - H) * (1 + H) = 0 := by
    have H2 : H * H = 1 := by
      have h_sq := HyperbolicGenerator.sq_eq_one (H := H)
      rw [sq] at h_sq
      exact h_sq
    simp only [add_mul, sub_mul, mul_sub, mul_add, one_mul, mul_one, H2]
    abel
  rw [h, smul_zero]

theorem hyperbolicKernel_eq_peirce (t : ℝ) :
    hyperbolicKernel H t =
      Real.exp t • peircePlus H + Real.exp (-t) • peirceMinus H := by
  unfold hyperbolicKernel peircePlus peirceMinus
  rw [Real.cosh_eq, Real.sinh_eq]
  module

theorem hyperbolicKernel_zero :
    hyperbolicKernel H 0 = 1 := by
  unfold hyperbolicKernel
  simp

theorem hyperbolicKernel_add [HyperbolicGenerator H] (s t : ℝ) :
    hyperbolicKernel H (s + t) = hyperbolicKernel H s * hyperbolicKernel H t := by
  unfold hyperbolicKernel
  rw [Real.cosh_add, Real.sinh_add]
  have h_sq : H * H = 1 := by
    have h := HyperbolicGenerator.sq_eq_one (H := H)
    rw [sq] at h
    exact h
  simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, h_sq]
  module

theorem hyperbolicKernel_neg_mul [HyperbolicGenerator H] (t : ℝ) :
    hyperbolicKernel H (-t) * hyperbolicKernel H t = 1 := by
  rw [← hyperbolicKernel_add H (-t) t, neg_add_cancel, hyperbolicKernel_zero]

/-- The algebra-valued elliptic kernel associated with a square-minus-one
generator. -/
noncomputable def ellipticKernel (J : A) (t : ℝ) : A :=
  Real.cos t • (1 : A) + Real.sin t • J

theorem ellipticKernel_zero (J : A) :
    ellipticKernel J 0 = 1 := by
  unfold ellipticKernel
  simp

theorem ellipticKernel_add (J : A) [EllipticGenerator J] (s t : ℝ) :
    ellipticKernel J (s + t) = ellipticKernel J s * ellipticKernel J t := by
  unfold ellipticKernel
  rw [Real.cos_add, Real.sin_add]
  have h_sq : J * J = -1 := by
    have h := EllipticGenerator.sq_eq_neg_one (J := J)
    rw [sq] at h
    exact h
  simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, h_sq,
    smul_neg, smul_one]
  module

theorem ellipticKernel_neg_mul (J : A) [EllipticGenerator J] (t : ℝ) :
    ellipticKernel J (-t) * ellipticKernel J t = 1 := by
  rw [← ellipticKernel_add J (-t) t, neg_add_cancel, ellipticKernel_zero]

/-- A loxodromic kernel combines commuting elliptic and hyperbolic sectors. -/
noncomputable def loxodromicKernel (J H : A) (theta t : ℝ) : A :=
  ellipticKernel J theta * hyperbolicKernel H t

theorem loxodromicKernel_add
    (J H : A) [EllipticGenerator J] [HyperbolicGenerator H]
    (hcomm : Commute J H) (theta₁ theta₂ t₁ t₂ : ℝ) :
    loxodromicKernel J H (theta₁ + theta₂) (t₁ + t₂) =
      loxodromicKernel J H theta₁ t₁ *
        loxodromicKernel J H theta₂ t₂ := by
  unfold loxodromicKernel
  rw [ellipticKernel_add J theta₁ theta₂,
    hyperbolicKernel_add H t₁ t₂]
  have hJ : J * J = -1 := by
    have h := EllipticGenerator.sq_eq_neg_one (J := J)
    rw [sq] at h
    exact h
  have hH : H * H = 1 := by
    have h := HyperbolicGenerator.sq_eq_one (H := H)
    rw [sq] at h
    exact h
  have hHJ : H * J = J * H := hcomm.eq.symm
  have hEH (a b : ℝ) :
      ellipticKernel J a * hyperbolicKernel H b =
        hyperbolicKernel H b * ellipticKernel J a := by
    unfold ellipticKernel hyperbolicKernel
    simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one,
      hJ, hH, hHJ, smul_neg, smul_one]
    module
  calc
    ellipticKernel J theta₁ * ellipticKernel J theta₂ *
        (hyperbolicKernel H t₁ * hyperbolicKernel H t₂) =
      ellipticKernel J theta₁ *
        (ellipticKernel J theta₂ * hyperbolicKernel H t₁) *
          hyperbolicKernel H t₂ := by simp only [mul_assoc]
    _ = ellipticKernel J theta₁ *
        (hyperbolicKernel H t₁ * ellipticKernel J theta₂) *
          hyperbolicKernel H t₂ := by rw [hEH]
    _ = ellipticKernel J theta₁ * hyperbolicKernel H t₁ *
        (ellipticKernel J theta₂ * hyperbolicKernel H t₂) := by
      simp only [mul_assoc]

theorem loxodromicKernel_zero (J H : A) :
    loxodromicKernel J H 0 0 = 1 := by
  unfold loxodromicKernel
  rw [ellipticKernel_zero, hyperbolicKernel_zero, one_mul]

theorem loxodromicKernel_neg_mul
    (J H : A) [EllipticGenerator J] [HyperbolicGenerator H]
    (hcomm : Commute J H) (theta t : ℝ) :
    loxodromicKernel J H (-theta) (-t) *
        loxodromicKernel J H theta t = 1 := by
  rw [← loxodromicKernel_add J H hcomm (-theta) theta (-t) t,
    neg_add_cancel, neg_add_cancel, loxodromicKernel_zero]

end SplitCliffordTransformKernel
