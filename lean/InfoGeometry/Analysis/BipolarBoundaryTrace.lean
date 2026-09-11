import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

noncomputable section
namespace InfoGeometry.Analysis.BipolarBoundaryTrace

def phiXY (x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (x ^ 2 + y ^ 2) -
    (1 / 2 : ℝ) * Real.log ((x - 1) ^ 2 + y ^ 2)

@[simp] theorem phiXY_half (y : ℝ) : phiXY (1 / 2) y = 0 := by
  unfold phiXY
  congr 1
  norm_num
theorem phiXY_reflection (x y : ℝ) :
    phiXY (1 - x) y = -phiXY x y := by
  unfold phiXY
  have h0 : (1 - x) ^ 2 = (x - 1) ^ 2 := by ring
  have h1 : ((1 - x) - 1) ^ 2 = x ^ 2 := by ring
  rw [h0, h1]
  ring

theorem hasDerivAt_phiXY {x y : ℝ}
    (h0 : x ^ 2 + y ^ 2 ≠ 0)
    (h1 : (x - 1) ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun t => phiXY t y)
      (x / (x ^ 2 + y ^ 2) - (x - 1) / ((x - 1) ^ 2 + y ^ 2)) x := by
  have hg0 : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id x).pow 2).add_const (y ^ 2)
  have hg1 : HasDerivAt (fun t : ℝ => (t - 1) ^ 2 + y ^ 2)
      (2 * (x - 1)) x := by
    have hsub : HasDerivAt (fun t : ℝ => t - 1) 1 x := by
      simpa using (hasDerivAt_id x).sub_const 1
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (hsub.pow 2).add_const (y ^ 2)
  have hlog0 := (Real.hasDerivAt_log h0).comp x hg0
  have hlog1 := (Real.hasDerivAt_log h1).comp x hg1
  have hmain := (hlog0.const_mul (1 / 2 : ℝ)).sub
    (hlog1.const_mul (1 / 2 : ℝ))
  convert hmain using 1 <;> ring

theorem hasDerivAt_phiXY_half (y : ℝ) :
    HasDerivAt (fun t => phiXY t y)
      (1 / ((1 / 4 : ℝ) + y ^ 2)) (1 / 2) := by
  have hpos : 0 < (1 / 4 : ℝ) + y ^ 2 := by
    nlinarith [sq_nonneg y]
  have h0 : ((1 / 2 : ℝ) ^ 2 + y ^ 2) ≠ 0 := by
    norm_num
    exact ne_of_gt hpos
  have h1 : (((1 / 2 : ℝ) - 1) ^ 2 + y ^ 2) ≠ 0 := by
    norm_num
    exact ne_of_gt hpos
  have h := hasDerivAt_phiXY (x := (1 / 2 : ℝ)) (y := y) h0 h1
  convert h using 1 <;> norm_num <;> field_simp [ne_of_gt hpos] <;> ring

/-- Derivative in the second real coordinate, away from both punctures. -/
theorem hasDerivAt_phiXY_second {x y : ℝ}
    (h0 : x ^ 2 + y ^ 2 ≠ 0)
    (h1 : (x - 1) ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun t => phiXY x t)
      (y / (x ^ 2 + y ^ 2) - y / ((x - 1) ^ 2 + y ^ 2)) y := by
  have hg (a : ℝ) : HasDerivAt (fun t : ℝ => a + t ^ 2) (2 * y) y := by
    simpa using ((hasDerivAt_id y).pow 2).const_add a
  have hlog0 := (Real.hasDerivAt_log h0).comp y (hg (x ^ 2))
  have hlog1 := (Real.hasDerivAt_log h1).comp y (hg ((x - 1) ^ 2))
  have hmain := (hlog0.const_mul (1 / 2 : ℝ)).sub
    (hlog1.const_mul (1 / 2 : ℝ))
  convert hmain using 1 <;> ring

theorem deriv_phiXY_half (y : ℝ) :
    deriv (fun t => phiXY t y) (1 / 2) = 1 / ((1 / 4 : ℝ) + y ^ 2) :=
  (hasDerivAt_phiXY_half y).deriv

/-- Chain rule for the real potential along a differentiable planar curve. -/
theorem hasDerivAt_phiXY_comp {f g : ℝ → ℝ} {t u v : ℝ}
    (hf : HasDerivAt f u t) (hg : HasDerivAt g v t)
    (h0 : f t ^ 2 + g t ^ 2 ≠ 0)
    (h1 : (f t - 1) ^ 2 + g t ^ 2 ≠ 0) :
    HasDerivAt (fun a => phiXY (f a) (g a))
      ((f t / (f t ^ 2 + g t ^ 2) -
          (f t - 1) / ((f t - 1) ^ 2 + g t ^ 2)) * u +
        (g t / (f t ^ 2 + g t ^ 2) -
          g t / ((f t - 1) ^ 2 + g t ^ 2)) * v) t := by
  have hl0 := ((hf.pow 2).add (hg.pow 2)).log h0
  have hl1 := (((hf.sub_const 1).pow 2).add (hg.pow 2)).log h1
  have hm := (hl0.const_mul (1 / 2 : ℝ)).sub (hl1.const_mul (1 / 2 : ℝ))
  convert hm using 1 <;> simp [phiXY, Pi.add_apply, Pi.pow_apply] <;> ring

theorem boundaryKernel_pos (y : ℝ) :
    0 < 1 / ((1 / 4 : ℝ) + y ^ 2) := by positivity

/-- The left restriction has the same coordinate derivative as the full
potential. This is not an outward-normal sign convention. -/
theorem derivWithin_phiXY_left (y : ℝ) :
    derivWithin (fun x => phiXY x y) (Set.Iic (1 / 2)) (1 / 2) =
      1 / ((1 / 4 : ℝ) + y ^ 2) := by
  exact (hasDerivAt_phiXY_half y).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Iic (1 / 2 : ℝ))

/-- The right restriction has the same coordinate derivative. -/
theorem derivWithin_phiXY_right (y : ℝ) :
    derivWithin (fun x => phiXY x y) (Set.Ici (1 / 2)) (1 / 2) =
      1 / ((1 / 4 : ℝ) + y ^ 2) := by
  exact (hasDerivAt_phiXY_half y).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Ici (1 / 2 : ℝ))

/-- The full two-puncture potential has no coordinate-derivative jump on the
bisector. A one-sided boundary-density model is a different construction. -/
theorem phiXY_derivative_jump_zero (y : ℝ) :
    derivWithin (fun x => phiXY x y) (Set.Ici (1 / 2)) (1 / 2) -
      derivWithin (fun x => phiXY x y) (Set.Iic (1 / 2)) (1 / 2) = 0 := by
  rw [derivWithin_phiXY_right, derivWithin_phiXY_left, sub_self]

theorem bipolar_boundary_trace_packet (y : ℝ) :
    phiXY (1 / 2) y = 0 ∧
      deriv (fun t => phiXY t y) (1 / 2) = 1 / ((1 / 4 : ℝ) + y ^ 2) ∧
      0 < 1 / ((1 / 4 : ℝ) + y ^ 2) := by
  exact ⟨phiXY_half y, deriv_phiXY_half y, boundaryKernel_pos y⟩

end InfoGeometry.Analysis.BipolarBoundaryTrace
