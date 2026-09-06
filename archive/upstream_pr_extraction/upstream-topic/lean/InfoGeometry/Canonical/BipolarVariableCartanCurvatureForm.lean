import InfoGeometry.Canonical.BipolarVariableConnectionAnalyticExterior
import Mathlib

/-!
# Bundled curvature form of the variable bipolar Cartan connection

The analytic directional-derivative owner proves that
`variableExteriorDerivativeAt` is the genuine entrywise alternation of the
base derivative of the point-dependent connection.  This file packages that
alternation as the repository-native `Op2Form` and states flatness as equality
of alternating operator-valued two-forms.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarVariableCartanCurvatureForm

open InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
open InfoGeometry.Canonical.BipolarVariableConnectionAnalyticExterior
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra

abbrev Matrix2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Bundled exterior derivative of the variable connection at a base point. -/
def variableExteriorDerivativeForm (s : ℂ) : Op2Form ℂ ℂ Matrix2C where
  toBilin := {
    toFun := fun u => {
      toFun := fun v => variableExteriorDerivativeAt s u v
      map_add' := by
        intro v w
        simp
      map_smul' := by
        intro c v
        simp
    }
    map_add' := by
      intro u v
      ext w
      simp
    map_smul' := by
      intro c u
      ext v
      simp
  }
  alt' := by
    intro u
    simp

@[simp] theorem variableExteriorDerivativeForm_apply
    (s u v : ℂ) :
    variableExteriorDerivativeForm s u v =
      variableExteriorDerivativeAt s u v :=
  rfl

/-- The bundled exterior derivative is the zero alternating two-form. -/
theorem variableExteriorDerivativeForm_eq_zero (s : ℂ) :
    variableExteriorDerivativeForm s = 0 := by
  apply Op2Form.ext
  intro u v
  simp

/-- Bundled curvature `dA + A wedge A` at the base point `s`. -/
def variableCartanCurvatureForm (s : ℂ) : Op2Form ℂ ℂ Matrix2C :=
  variableExteriorDerivativeForm s +
    wedge (variableCartanConnection s) (variableCartanConnection s)

/-- The point-dependent logarithmic Cartan connection is flat as an equality
of native alternating operator-valued two-forms. -/
theorem variableCartanCurvatureForm_eq_zero (s : ℂ) :
    variableCartanCurvatureForm s = 0 := by
  rw [variableCartanCurvatureForm,
    variableExteriorDerivativeForm_eq_zero,
    variableCartanConnection_selfWedge_zero]
  simp

/-- The bundled theorem agrees pointwise with the earlier local curvature
formula. -/
theorem variableCartanCurvatureForm_apply_eq_local
    (s u v : ℂ) :
    variableCartanCurvatureForm s u v =
      variableCartanCurvatureAt s u v := by
  simp [variableCartanCurvatureForm, variableCartanCurvatureAt]

/-- Analytically witnessed bundled flatness on the punctured domain. -/
theorem bipolar_variable_curvature_form_packet
    {s : ℂ} (hs : s ∈
      InfoGeometry.Analysis.BipolarCrossRatioLog.punctured01)
    (u v : ℂ) (i j : Fin 2) :
    HasDerivAt
      (fun t : ℂ => variableCartanConnection (s + t * u) v i j)
      (connectionDirectionalDerivative s u v i j) 0 ∧
      variableExteriorDerivativeForm s = 0 ∧
      variableCartanCurvatureForm s = 0 := by
  exact ⟨hasDerivAt_variableCartanConnection_entry_along hs u v i j,
    variableExteriorDerivativeForm_eq_zero s,
    variableCartanCurvatureForm_eq_zero s⟩

end InfoGeometry.Canonical.BipolarVariableCartanCurvatureForm
