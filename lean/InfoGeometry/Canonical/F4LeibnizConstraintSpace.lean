import InfoGeometry.Canonical.F4LeibnizConstraintSpaceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Native compatibility surface for the upstream F₄ Leibniz constraint path.

The residual and coordinate readout are owned by the active bridge; this file
restores the historical names without introducing a second constraint map or
promoting the open rank certificate.
-/

namespace InfoGeometry.Canonical.F4LeibnizConstraintSpace

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.F4LeibnizConstraintSpaceBridge

abbrev H3 := H3Zorn ℝ
abbrev EndH3 := Module.End ℝ H3
abbrev ActionCoord := Fin 27 → Fin 27 → ℝ
abbrev ConstraintCoord := Fin 27 → Fin 27 → Fin 27 → ℝ

noncomputable abbrev f4Readout := actionReadout
noncomputable abbrev f4ReadoutLM := actionReadoutLM

theorem f4Readout_injective : Function.Injective f4ReadoutLM :=
  actionReadoutLM_injective

noncomputable abbrev leibnizResidual := residualReadout

theorem f4_derivation_constraint_coordinates_zero
    (D : EndH3) (hD : H3ZornJordanDerivation D) :
    leibnizResidual D = 0 := by
  exact derivation_residual_readout_zero D hD

def f4_constraint_rank_closure_debt : String :=
  "Open computational certificate: flatten the native Leibniz residual readout and certify its rational rank."

end InfoGeometry.Canonical.F4LeibnizConstraintSpace
