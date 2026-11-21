/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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
open InfoGeometry.Canonical.F4LeibnizResidualBridge
open InfoGeometry.Canonical.H3ZornBasis

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



/-- Linear finite-coordinate readout of a bilinear residual. -/
noncomputable def constraintReadoutLM :
    (H3 →ₗ[ℝ] H3 →ₗ[ℝ] H3) →ₗ[ℝ] ConstraintCoord where
  toFun := constraintReadout
  map_add' B C := by
    funext i j k
    simp [constraintReadout]
  map_smul' a B := by
    funext i j k
    simp [constraintReadout]

/-- The finite Leibniz constraint matrix map on arbitrary Albert endomorphisms. -/
noncomputable def f4ConstraintCoordinateMap : EndH3 →ₗ[ℝ] ConstraintCoord where
  toFun := residualReadout
  map_add' D E := by
    funext i j k
    simp [residualReadout, F4LeibnizResidualBridge.residual, map_add, mul_add, add_mul,
      sub_eq_add_neg]
    abel
  map_smul' a D := by
    funext i j k
    simp [residualReadout, F4LeibnizResidualBridge.residual, map_smul, smul_mul_assoc,
      mul_smul_comm]
    ring

@[simp] theorem f4ConstraintCoordinateMap_apply
    (D : EndH3) (i j k : Fin 27) :
    f4ConstraintCoordinateMap D i j k =
      (h3ZornCoordinateBasis.repr
        (F4LeibnizResidualBridge.residual D
          (h3ZornCoordinateBasis i) (h3ZornCoordinateBasis j))) k := rfl

theorem constraint_equation_count : 27 * 27 * 27 = 19683 := by norm_num

theorem required_constraint_rank : 729 - 52 = 677 := by norm_num

end InfoGeometry.Canonical.F4LeibnizConstraintSpace
