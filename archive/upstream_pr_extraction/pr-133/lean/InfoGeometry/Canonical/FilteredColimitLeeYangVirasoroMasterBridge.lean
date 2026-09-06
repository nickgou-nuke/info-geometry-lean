import Mathlib.Tactic
import InfoGeometry.Canonical.ModuleCatDirectLimitKernelSurvivalBridge
import InfoGeometry.Canonical.SpinChainLogCFTLeeYangMasterBridge
import InfoGeometry.Canonical.InfiniteVirasoroVOAFusionBridge
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Finite contraction root readout

This module contains one elementary complex-algebra statement.  The imported
colimit, Lee--Yang, and Virasoro modules are not turned into a combined
analytic theorem here.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredColimitLeeYangVirasoroMasterBridge

open Complex
open InfoGeometry.Canonical.ModuleCatDirectLimitKernelSurvivalBridge
open InfoGeometry.Canonical.SpinChainLogCFTLeeYangMasterBridge
open InfoGeometry.Canonical.InfiniteVirasoroVOAFusionBridge
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/--
**Finite contracted-root equation.**
If `a*z + d = 0` and `a ≠ 0`, then `z = -d/a`; the determinant premise is
retained as part of the supplied contraction data.
-/
theorem asano_contraction_quadratic_preserved (a b c d z : ℂ) (h_det : a * d - b * c ≠ 0) (h_root : a * z + d = 0) (ha : a ≠ 0) :
    z = - d / a := by
  have h1 : a * z = -d := eq_neg_of_add_eq_zero_left h_root
  have h1_comm : z * a = -d := by rw [mul_comm, h1]
  exact eq_div_of_mul_eq ha h1_comm

end InfoGeometry.Canonical.FilteredColimitLeeYangVirasoroMasterBridge
