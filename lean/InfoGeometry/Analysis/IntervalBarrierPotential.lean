import InfoGeometry.Analysis.LogHomogeneousPotential

/-!
# Exact interval strain-barrier calculus

The scalar restriction of `-log det(Λ²I - FᵀF)` is `-log(Λ²-x²)`.
Its Hessian is positive on the interval, and its normalized zero occurs in
the interior. A sublevel bound implies a gap to the wall; no PDE propagation
of that bound is assumed or asserted here.
-/

noncomputable section

namespace InfoGeometry.Analysis.IntervalBarrierPotential

open LogHomogeneousPotential

def barrier (L x : ℝ) : ℝ := logPotential (fun y => L ^ 2 - y ^ 2) x
def slope (L x : ℝ) : ℝ := 2 * x / (L ^ 2 - x ^ 2)

theorem hasDerivAt_barrier (L x : ℝ) (hx : x ^ 2 < L ^ 2) :
    HasDerivAt (barrier L) (slope L x) x := by
  convert (((hasDerivAt_const x (L ^ 2)).sub (hasDerivAt_pow 2 x)).log
    (ne_of_gt (sub_pos.mpr hx))).neg using 1
  simp [slope]
  ring

theorem hasDerivAt_slope (L x : ℝ) (hx : x ^ 2 < L ^ 2) :
    HasDerivAt (slope L) (2 * (L ^ 2 + x ^ 2) / (L ^ 2 - x ^ 2) ^ 2) x := by
  convert (((hasDerivAt_id x).const_mul 2).div
    ((hasDerivAt_const x (L ^ 2)).sub (hasDerivAt_pow 2 x))
    (ne_of_gt (sub_pos.mpr hx))) using 1
  simp
  ring

theorem barrier_second_derivative (L x : ℝ) (hx : x ^ 2 < L ^ 2) :
    deriv (deriv (barrier L)) x = 2 * (L ^ 2 + x ^ 2) / (L ^ 2 - x ^ 2) ^ 2 := by
  have hlocal : deriv (barrier L) =ᶠ[nhds x] slope L := by
    filter_upwards [(continuousAt_id.pow 2).eventually_lt_const hx] with y hy
    exact (hasDerivAt_barrier L y hy).deriv
  rw [hlocal.deriv_eq, (hasDerivAt_slope L x hx).deriv]

theorem hessian_pos (L x : ℝ) (hx : x ^ 2 < L ^ 2) :
    0 < deriv (deriv (barrier L)) x := by
  rw [barrier_second_derivative L x hx]
  apply div_pos
  · nlinarith [sq_nonneg x]
  · exact sq_pos_of_pos (sub_pos.mpr hx)

theorem normalized_zero_has_positive_hessian :
    barrier 1 0 = 0 ∧ 0 ^ 2 < (1 : ℝ) ^ 2 ∧ deriv (deriv (barrier 1)) 0 = 2 := by
  refine ⟨by norm_num [barrier, logPotential], by norm_num, ?_⟩
  rw [barrier_second_derivative 1 0 (by norm_num)]
  norm_num

theorem sublevel_strain_gap (L x C : ℝ) (hx : x ^ 2 < L ^ 2)
    (hC : barrier L x ≤ C) : x ^ 2 ≤ L ^ 2 - Real.exp (-C) := by
  have h := sublevel_gap (fun y => L ^ 2 - y ^ 2) x (sub_pos.mpr hx) C hC
  linarith

end InfoGeometry.Analysis.IntervalBarrierPotential
