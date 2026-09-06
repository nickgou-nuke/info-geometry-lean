import InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
import Mathlib

/-!
# Analytic witness for the variable Cartan exterior derivative

The local exterior derivative in
`BipolarVariableCartanMaurerCartan` is defined by alternating a displayed
base-directional derivative.  This file proves, entry by entry, that the
displayed matrix is the genuine complex derivative of the point-dependent
connection evaluated along an affine tangent direction.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarVariableConnectionAnalyticExterior

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
open InfoGeometry.Physics.ChiralCausalCone

/-- Every matrix entry of `A_{s+t u}(v)` has the derivative used in the local
exterior derivative. -/
theorem hasDerivAt_variableCartanConnection_entry_along
    {s : ℂ} (hs : s ∈ punctured01)
    (u v : ℂ) (i j : Fin 2) :
    HasDerivAt
      (fun t : ℂ => variableCartanConnection (s + t * u) v i j)
      (connectionDirectionalDerivative s u v i j) 0 := by
  have hω := hasDerivAt_omegaCoeff_along hs u
  fin_cases i <;> fin_cases j
  · have h := (hω.mul_const v).div_const 2
    convert h using 1 <;>
      simp [variableCartanConnection, connectionDirectionalDerivative,
        σ3c, Matrix.smul_apply] <;>
      ring
  · simpa [variableCartanConnection, connectionDirectionalDerivative,
      σ3c, Matrix.smul_apply] using
      (hasDerivAt_const (x := (0 : ℂ)) (c := (0 : ℂ)))
  · simpa [variableCartanConnection, connectionDirectionalDerivative,
      σ3c, Matrix.smul_apply] using
      (hasDerivAt_const (x := (0 : ℂ)) (c := (0 : ℂ)))
  · have h := ((hω.mul_const v).div_const 2).neg
    convert h using 1 <;>
      simp [variableCartanConnection, connectionDirectionalDerivative,
        σ3c, Matrix.smul_apply] <;>
      ring

/-- The two directional derivatives entering `dA(u,v)` are both genuine
entrywise derivatives. -/
theorem variableExteriorDerivative_analytic_witness
    {s : ℂ} (hs : s ∈ punctured01)
    (u v : ℂ) (i j : Fin 2) :
    HasDerivAt
      (fun t : ℂ => variableCartanConnection (s + t * u) v i j)
      (connectionDirectionalDerivative s u v i j) 0 ∧
    HasDerivAt
      (fun t : ℂ => variableCartanConnection (s + t * v) u i j)
      (connectionDirectionalDerivative s v u i j) 0 := by
  exact ⟨hasDerivAt_variableCartanConnection_entry_along hs u v i j,
    hasDerivAt_variableCartanConnection_entry_along hs v u i j⟩

/-- Analytically witnessed Maurer--Cartan packet on the punctured domain. -/
theorem variableCartanMaurerCartan_analytic
    {s : ℂ} (hs : s ∈ punctured01)
    (u v : ℂ) (i j : Fin 2) :
    HasDerivAt
      (fun t : ℂ => variableCartanConnection (s + t * u) v i j)
      (connectionDirectionalDerivative s u v i j) 0 ∧
    HasDerivAt
      (fun t : ℂ => variableCartanConnection (s + t * v) u i j)
      (connectionDirectionalDerivative s v u i j) 0 ∧
    variableExteriorDerivativeAt s u v = 0 ∧
    wedge (variableCartanConnection s)
      (variableCartanConnection s) u v = 0 ∧
    variableCartanCurvatureAt s u v = 0 := by
  exact ⟨hasDerivAt_variableCartanConnection_entry_along hs u v i j,
    hasDerivAt_variableCartanConnection_entry_along hs v u i j,
    variableExteriorDerivativeAt_eq_zero s u v,
    by rw [variableCartanConnection_selfWedge_zero]; rfl,
    variableCartanMaurerCartan s u v⟩

end InfoGeometry.Canonical.BipolarVariableConnectionAnalyticExterior
