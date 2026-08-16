import Mathlib.Analysis.SpecialFunctions.Exp
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

theorem barrier_eq_neg_log_product (x : PositiveHomogeneousCone) :
    barrier x = -Real.log (x.1.1 * x.1.2) := by
  unfold barrier
  rw [Real.log_mul (ne_of_gt x.2.1) (ne_of_gt x.2.2)]
  ring

theorem barrier_cartanFlow_invariant
    (t : ℝ) (x : PositiveHomogeneousCone) :
    barrier (cartanFlow t x) = barrier x := by
  rw [barrier_eq_neg_log_product, barrier_eq_neg_log_product]
  rw [cartanFlow_product]

theorem barrier_cartanFlow_invariant_of_product
    (t : ℝ) (x : PositiveHomogeneousCone)
    (hprod : (cartanFlow t x).1.1 * (cartanFlow t x).1.2 = x.1.1 * x.1.2) :
    barrier (cartanFlow t x) = barrier x := by
  rw [barrier_eq_neg_log_product, barrier_eq_neg_log_product, hprod]

end

end InfoGeometry.Canonical.PositiveHomogeneousBarrier
