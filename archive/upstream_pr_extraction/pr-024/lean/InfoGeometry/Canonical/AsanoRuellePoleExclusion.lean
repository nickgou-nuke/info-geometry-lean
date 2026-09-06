import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Ring.Basic

/-!
# InfoGeometry.Canonical.AsanoRuellePoleExclusion

Algebraic pole-exclusion lemmas for the nondegenerate Asano-Ruelle setting.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.AsanoRuelle

variable {K : Type*} [CommRing K]

/--
Left pole determinant identity.
-/
theorem asano_pole_eval_left
    (A B C D z1 z2 : K)
    (h_pole : C + D * z1 = 0) :
    D * (A + B * z1 + C * z2 + D * z1 * z2) = A * D - B * C := by
  linear_combination (B + D * z2) * h_pole

/--
Right pole determinant identity.
-/
theorem asano_pole_eval_right
    (A B C D z1 z2 : K)
    (h_pole : B + D * z2 = 0) :
    D * (A + B * z1 + C * z2 + D * z1 * z2) = A * D - B * C := by
  linear_combination (C + D * z1) * h_pole

/--
Strict zero-freeness at the left pole under nondegeneracy.
-/
theorem asano_phi_ne_zero_at_left_pole
    (A B C D z1 z2 : K) [IsDomain K]
    (h_nondeg : A * D - B * C ≠ 0)
    (h_pole : C + D * z1 = 0) :
    A + B * z1 + C * z2 + D * z1 * z2 ≠ 0 := by
  intro h_phi
  have h_eval := asano_pole_eval_left A B C D z1 z2 h_pole
  rw [h_phi, mul_zero] at h_eval
  exact h_nondeg h_eval.symm

/--
Strict zero-freeness at the right pole under nondegeneracy.
-/
theorem asano_phi_ne_zero_at_right_pole
    (A B C D z1 z2 : K) [IsDomain K]
    (h_nondeg : A * D - B * C ≠ 0)
    (h_pole : B + D * z2 = 0) :
    A + B * z1 + C * z2 + D * z1 * z2 ≠ 0 := by
  intro h_phi
  have h_eval := asano_pole_eval_right A B C D z1 z2 h_pole
  rw [h_phi, mul_zero] at h_eval
  exact h_nondeg h_eval.symm

end InfoGeometry.AsanoRuelle

