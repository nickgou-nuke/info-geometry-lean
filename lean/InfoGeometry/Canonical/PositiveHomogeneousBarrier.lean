import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Positive homogeneous logarithmic barrier

The barrier is defined on the real positive homogeneous cone only.  This file
does not identify that cone with the complex homogeneous spectral carrier and
does not assert a self-concordance theorem.
-/

namespace InfoGeometry.Canonical.PositiveHomogeneousBarrier

noncomputable section

/-- The real positive two-lane homogeneous cone. -/
def PositiveHomogeneousCone : Type :=
  {x : ℝ × ℝ // 0 < x.1 ∧ 0 < x.2}

/-- The logarithmic barrier `-log p - log q` on the positive cone. -/
def barrier (x : PositiveHomogeneousCone) : ℝ :=
  -Real.log x.1.1 - Real.log x.1.2

/-- The split Cartan flow on the two homogeneous lanes. -/
def cartanFlow (t : ℝ) (x : PositiveHomogeneousCone) :
    PositiveHomogeneousCone :=
  ⟨(Real.exp t * x.1.1, Real.exp (-t) * x.1.2), by
    exact ⟨mul_pos (Real.exp_pos _) x.2.1,
      mul_pos (Real.exp_pos _) x.2.2⟩⟩

/-- Reciprocal rescaling of the two positive homogeneous lanes. -/
def reciprocalScale (lambda : ℝ) (x : PositiveHomogeneousCone)
    (hlambda : 0 < lambda) : PositiveHomogeneousCone :=
  ⟨(lambda * x.1.1, lambda⁻¹ * x.1.2), by
    exact ⟨mul_pos hlambda x.2.1,
      mul_pos (inv_pos.mpr hlambda) x.2.2⟩⟩

@[simp]
theorem reciprocalScale_fst (lambda : ℝ) (x : PositiveHomogeneousCone)
    (hlambda : 0 < lambda) :
    (reciprocalScale lambda x hlambda).1.1 = lambda * x.1.1 :=
  rfl

@[simp]
theorem reciprocalScale_snd (lambda : ℝ) (x : PositiveHomogeneousCone)
    (hlambda : 0 < lambda) :
    (reciprocalScale lambda x hlambda).1.2 = lambda⁻¹ * x.1.2 :=
  rfl

theorem reciprocalScale_product (lambda : ℝ) (x : PositiveHomogeneousCone)
    (hlambda : 0 < lambda) :
    (reciprocalScale lambda x hlambda).1.1 *
        (reciprocalScale lambda x hlambda).1.2 =
      x.1.1 * x.1.2 := by
  simp only [reciprocalScale_fst, reciprocalScale_snd]
  calc
    (lambda * x.1.1) * (lambda⁻¹ * x.1.2) =
        (lambda * lambda⁻¹) * (x.1.1 * x.1.2) := by ring
    _ = x.1.1 * x.1.2 := by
      rw [mul_inv_cancel₀ (ne_of_gt hlambda), one_mul]

@[simp]
theorem reciprocalScale_one (x : PositiveHomogeneousCone) :
    reciprocalScale 1 x one_pos = x := by
  apply Subtype.ext
  ext <;> simp [reciprocalScale]

theorem reciprocalScale_mul
    (lambda mu : ℝ) (x : PositiveHomogeneousCone)
    (hlambda : 0 < lambda) (hmu : 0 < mu) :
    reciprocalScale (lambda * mu) x (mul_pos hlambda hmu) =
      reciprocalScale lambda (reciprocalScale mu x hmu) hlambda := by
  apply Subtype.ext
  ext <;> dsimp [reciprocalScale]
  · ring
  · field_simp [ne_of_gt hlambda, ne_of_gt hmu]

theorem reciprocalScale_inv
    (lambda : ℝ) (x : PositiveHomogeneousCone) (hlambda : 0 < lambda) :
    reciprocalScale lambda⁻¹ (reciprocalScale lambda x hlambda)
        (inv_pos.mpr hlambda) = x := by
  have hcomp := reciprocalScale_mul lambda⁻¹ lambda x
    (inv_pos.mpr hlambda) hlambda
  simpa [inv_mul_cancel₀ (ne_of_gt hlambda)] using hcomp.symm

theorem cartanFlow_eq_reciprocalScale
    (t : ℝ) (x : PositiveHomogeneousCone) :
    reciprocalScale (Real.exp t) x (Real.exp_pos t) = cartanFlow t x := by
  apply Subtype.ext
  ext <;> simp [reciprocalScale, cartanFlow, Real.exp_neg]

@[simp]
theorem cartanFlow_fst (t : ℝ) (x : PositiveHomogeneousCone) :
    (cartanFlow t x).1.1 = Real.exp t * x.1.1 :=
  rfl

@[simp]
theorem cartanFlow_snd (t : ℝ) (x : PositiveHomogeneousCone) :
    (cartanFlow t x).1.2 = Real.exp (-t) * x.1.2 :=
  rfl

theorem cartanFlow_product (t : ℝ) (x : PositiveHomogeneousCone) :
    (cartanFlow t x).1.1 * (cartanFlow t x).1.2 = x.1.1 * x.1.2 := by
  simp only [cartanFlow_fst, cartanFlow_snd]
  calc
    Real.exp t * x.1.1 * (Real.exp (-t) * x.1.2) =
        (Real.exp t * Real.exp (-t)) * (x.1.1 * x.1.2) := by ring
    _ = x.1.1 * x.1.2 := by
      rw [← Real.exp_add]
      norm_num

theorem cartanFlow_zero (x : PositiveHomogeneousCone) :
    cartanFlow 0 x = x := by
  apply Subtype.ext
  ext <;> simp [cartanFlow]

theorem cartanFlow_add (s t : ℝ) (x : PositiveHomogeneousCone) :
    cartanFlow (s + t) x = cartanFlow s (cartanFlow t x) := by
  apply Subtype.ext
  ext
  · simp only [cartanFlow]
    rw [Real.exp_add]
    ring
  · simp only [cartanFlow]
    rw [neg_add, Real.exp_add]
    ring

theorem cartanFlow_neg (t : ℝ) (x : PositiveHomogeneousCone) :
    cartanFlow (-t) (cartanFlow t x) = x := by
  rw [← cartanFlow_add]
  simp [cartanFlow_zero]

theorem cartanFlow_neg_right (t : ℝ) (x : PositiveHomogeneousCone) :
    cartanFlow t (cartanFlow (-t) x) = x := by
  rw [← cartanFlow_add]
  simp [cartanFlow_zero]

theorem cartanFlow_comm (s t : ℝ) (x : PositiveHomogeneousCone) :
    cartanFlow s (cartanFlow t x) = cartanFlow t (cartanFlow s x) := by
  rw [← cartanFlow_add, ← cartanFlow_add, add_comm]

theorem cartanFlow_injective (t : ℝ) :
    Function.Injective (cartanFlow t) := by
  intro x y hxy
  have h := congrArg (cartanFlow (-t)) hxy
  simpa only [cartanFlow_neg] using h

theorem cartanFlow_surjective (t : ℝ) :
    Function.Surjective (cartanFlow t) := by
  intro y
  exact ⟨cartanFlow (-t) y, cartanFlow_neg_right t y⟩

theorem cartanFlow_bijective (t : ℝ) :
    Function.Bijective (cartanFlow t) :=
  ⟨cartanFlow_injective t, cartanFlow_surjective t⟩

theorem barrier_eq_neg_log_product (x : PositiveHomogeneousCone) :
    barrier x = -Real.log (x.1.1 * x.1.2) := by
  unfold barrier
  rw [Real.log_mul (ne_of_gt x.2.1) (ne_of_gt x.2.2)]
  ring

theorem barrier_reciprocalScale_invariant
    (lambda : ℝ) (x : PositiveHomogeneousCone) (hlambda : 0 < lambda) :
    barrier (reciprocalScale lambda x hlambda) = barrier x := by
  rw [barrier_eq_neg_log_product, barrier_eq_neg_log_product]
  exact congrArg (fun z : ℝ => -Real.log z)
    (reciprocalScale_product lambda x hlambda)

theorem barrier_cartanFlow_invariant
    (t : ℝ) (x : PositiveHomogeneousCone) :
    barrier (cartanFlow t x) = barrier x := by
  rw [barrier_eq_neg_log_product, barrier_eq_neg_log_product]
  rw [cartanFlow_product]

/-- The homogeneous swap on the positive two-lane cone. -/
def homogeneousSwap (x : PositiveHomogeneousCone) :
    PositiveHomogeneousCone :=
  ⟨(x.1.2, x.1.1), ⟨x.2.2, x.2.1⟩⟩

@[simp]
theorem homogeneousSwap_fst (x : PositiveHomogeneousCone) :
    (homogeneousSwap x).1.1 = x.1.2 :=
  rfl

@[simp]
theorem homogeneousSwap_snd (x : PositiveHomogeneousCone) :
    (homogeneousSwap x).1.2 = x.1.1 :=
  rfl

theorem homogeneousSwap_involutive (x : PositiveHomogeneousCone) :
    homogeneousSwap (homogeneousSwap x) = x := by
  apply Subtype.ext
  rfl

theorem barrier_homogeneousSwap_invariant (x : PositiveHomogeneousCone) :
    barrier (homogeneousSwap x) = barrier x := by
  rw [barrier_eq_neg_log_product, barrier_eq_neg_log_product]
  simp only [homogeneousSwap_fst, homogeneousSwap_snd]
  rw [mul_comm]

theorem homogeneousSwap_reciprocalScale_conjugacy
    (lambda : ℝ) (x : PositiveHomogeneousCone) (hlambda : 0 < lambda) :
    homogeneousSwap (reciprocalScale lambda (homogeneousSwap x) hlambda) =
      reciprocalScale lambda⁻¹ x (inv_pos.mpr hlambda) := by
  apply Subtype.ext
  ext <;> dsimp [homogeneousSwap, reciprocalScale]
  · simp [inv_inv]

theorem homogeneousSwap_cartanFlow_conjugacy (t : ℝ) (x : PositiveHomogeneousCone) :
    homogeneousSwap (cartanFlow t (homogeneousSwap x)) =
      cartanFlow (-t) x := by
  apply Subtype.ext
  ext <;> simp [homogeneousSwap, cartanFlow, Real.exp_neg]

theorem barrier_cartanFlow_invariant_of_product
    (t : ℝ) (x : PositiveHomogeneousCone)
    (hprod : (cartanFlow t x).1.1 * (cartanFlow t x).1.2 = x.1.1 * x.1.2) :
    barrier (cartanFlow t x) = barrier x := by
  rw [barrier_eq_neg_log_product, barrier_eq_neg_log_product, hprod]

end

end InfoGeometry.Canonical.PositiveHomogeneousBarrier
