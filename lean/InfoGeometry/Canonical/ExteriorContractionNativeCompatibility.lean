/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KahlerAtiyahCartanForms
import InfoGeometry.Canonical.ExteriorContractionOperatorBridge
import InfoGeometry.Canonical.FockNumberOperatorBridge

/-!
# Equality of the real exterior operator realizations

The canonical contraction and occupation bridges use the same native real
exterior operators as the Kähler--Atiyah owner. These are equalities on the
actual carriers, with no identification of a space with its dual.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExteriorContractionNativeCompatibility

open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.CARSpinorCliffordActionBridge
open InfoGeometry.Canonical.SpinorMixedCARBridge
open InfoGeometry.Canonical.FockNumberOperatorBridge
open InfoGeometry.Canonical.KahlerAtiyahCartanForms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Both contraction owners select the same native operator over the reals. -/
theorem contractionOp_eq_contractionOperator (φ : Module.Dual ℝ V) :
    contractionOp φ = contractionOperator φ :=
  rfl

/-- Creation on the real dual exterior algebra is the native wedge action. -/
theorem creationOp_eq_wedgeOperator_apply (alpha : Module.Dual ℝ V)
    (omega : ExteriorAlgebra ℝ (Module.Dual ℝ V)) :
    creationOp alpha omega = wedgeOperator alpha omega :=
  rfl

/-- Occupation is the product of native Kähler--Atiyah creation and contraction. -/
theorem singleModeNumberEnd_eq_wedge_contraction (alpha : Module.Dual ℝ V) (u : V) :
    singleModeNumberEnd alpha u =
      wedgeOperator alpha * contractionOperator (evaluationLinear u) :=
  rfl

end InfoGeometry.Canonical.ExteriorContractionNativeCompatibility
