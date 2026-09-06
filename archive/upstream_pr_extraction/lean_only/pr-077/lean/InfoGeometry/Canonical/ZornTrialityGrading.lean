import Mathlib
import InfoGeometry.Canonical.ThreeColorZornScalingObstruction

/-!
# Discrete cubic triality parameter

This owner packages the primitive complex cubic root and applies the existing
generator-level scaling obstruction.  It does not claim a full automorphism
theorem for the native Zorn carrier or a topological direct-sum decomposition.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics.SplitOctonionBraidSU3
open InfoGeometry.Canonical.ThreeColorZornScalingObstruction

noncomputable def trialityParameter : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 3)

theorem trialityParameter_cube : trialityParameter ^ 3 = 1 := by
  dsimp [trialityParameter]
  rw [← Complex.exp_nat_mul]
  have h : ((3 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 3) =
      2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_two_pi_mul_I]

theorem trialityParameter_sq_eq_inv : trialityParameter ^ 2 = trialityParameter⁻¹ := by
  have hcube := trialityParameter_cube
  have hne : trialityParameter ≠ 0 := by
    exact Complex.exp_ne_zero _
  field_simp [hne]
  simpa [pow_succ, mul_assoc] using hcube

theorem triality_generator_covariance :
    zornMul (zornScale trialityParameter (E_k 0))
        (zornScale trialityParameter (E_k 1)) =
      zornScale trialityParameter (zornMul (E_k 0) (E_k 1)) := by
  apply (zornScale_upper_product_defect trialityParameter
    (Complex.exp_ne_zero _)).mpr
  exact trialityParameter_cube

end InfoGeometry.Canonical
