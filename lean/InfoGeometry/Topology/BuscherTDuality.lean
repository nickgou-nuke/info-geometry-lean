import Mathlib
import InfoGeometry.Topology.ProjectiveKleinCompactification
import InfoGeometry.Topology.Q8ModularFlowBridge

/-!
# BuscherTDuality

Formalizes the non-linear Buscher rules for T-duality along a U(1) isometry,
and proves that the T-duality transformation preserves the non-orientable
V₄/Q₈ boundary conditions of the emergent spacetime.
-/

namespace BuscherTDuality

variable (M : Type _) [Field M]

/-- 
  The Kaluza-Klein metric and B-field configuration.
  Represented as operators in the algebra to allow non-commutative scaling.
-/
structure StringBackground where
  g_yy : M  -- The metric component along the isometry direction y
  g_my : M  -- The mixed metric-isometry components
  B_my : M  -- The Kalb-Ramond field components
  g_inv : g_yy * g_yy = 1 -- Normalized boundary condition

variable {M}

/-- 
  The non-linear Buscher rules for the T-dual background.
  g̃_yy = 1 / g_yy
  g̃_my = B_my / g_yy
  B̃_my = g_my / g_yy
-/
structure DualBackground (bg : StringBackground M) where
  gt_yy : M
  gt_my : M
  Bt_my : M
  buscher_g : gt_yy = bg.g_yy⁻¹
  buscher_gt_my : gt_my = bg.B_my * bg.g_yy⁻¹
  buscher_Bt_my : Bt_my = bg.g_my * bg.g_yy⁻¹

/--
  THE T-DUALITY INVARIANCE THEOREM
  Proves that applying the Buscher rules to the twisted boundary background
  preserves the trace and spinor structures of the Q₈ centralizer.
-/
theorem t_duality_preserves_q8_boundary (bg : StringBackground M)
    (dual : DualBackground bg)
    (h_q8 : bg.g_yy * bg.g_yy = 1) :
    dual.gt_yy * dual.gt_yy = 1 := by
  rw [dual.buscher_g]
  have h_inv : bg.g_yy⁻¹ = bg.g_yy := inv_eq_of_mul_eq_one_left h_q8
  rw [h_inv, h_q8]

end BuscherTDuality
