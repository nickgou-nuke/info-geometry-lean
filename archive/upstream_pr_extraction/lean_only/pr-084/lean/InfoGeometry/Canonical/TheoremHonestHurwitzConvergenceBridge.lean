import Mathlib.Tactic
import InfoGeometry.Canonical.FilteredColimitLeeYangVirasoroMasterBridge
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/-!
# Finite Euler-factor and closed-circle readouts

This module contains two independent elementary statements:

1. For `0 < x < 1`, the reciprocal factor `(1 - x)⁻¹` is larger than `x`.

2. A convergent sequence of points with norm one has a norm-one limit.

No polynomial zero-transfer theorem, Hurwitz theorem, Cayley converse, or
analytic continuation is inferred by this file.
-/

noncomputable section

namespace InfoGeometry.Canonical.TheoremHonestHurwitzConvergenceBridge

open Complex
open InfoGeometry.Canonical.FilteredColimitLeeYangVirasoroMasterBridge
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/--
**Finite reciprocal-factor inequality.**
For `0 < x < 1`, `(1 - x)⁻¹ > x`.
-/
theorem bosonic_euler_factor_gt_prime_term {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (1 - x)⁻¹ > x := by
  have h1 : 0 < 1 - x := sub_pos.mpr hx1
  have hx1_sub : 1 - x < 1 := by linarith
  have h2 : 1 < (1 - x)⁻¹ := (one_lt_inv₀ h1).mpr hx1_sub
  exact hx1.trans h2

/--
**Closedness of the norm-one locus.**
A convergent sequence of complex points with norm one has norm-one limit.
-/
theorem hurwitz_unit_circle_limit_closed
    (z_seq : ℕ → ℂ) (z0 : ℂ)
    (h_circle : ∀ N, ‖z_seq N‖ = 1)
    (h_lim : Filter.Tendsto z_seq Filter.atTop (nhds z0)) :
    ‖z0‖ = 1 := by
  have h_norm_lim := h_lim.norm
  have h_const : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) := tendsto_const_nhds
  have h_eq : (fun N => ‖z_seq N‖) = fun _ => 1 := by
    ext N
    exact h_circle N
  rw [h_eq] at h_norm_lim
  exact tendsto_nhds_unique h_norm_lim h_const

end InfoGeometry.Canonical.TheoremHonestHurwitzConvergenceBridge
