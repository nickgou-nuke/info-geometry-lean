import Mathlib
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Canonical.ZornChiralPeirceDecomposition

/-!
# Four-corner Peirce soldering for the native Zorn carrier

The products in this file are explicitly left-associated through
`peirceComponent`; no associativity of the Zorn product is assumed.
-/

namespace InfoGeometry.Canonical

open ZornMatrix
open ZornClifford

abbrev ChiralZorn := ZornMatrix ℚ

def cornerPP (X : ChiralZorn) : ChiralZorn :=
  peirceComponent zornPlus zornPlus X

def cornerPM (X : ChiralZorn) : ChiralZorn :=
  peirceComponent zornPlus zornMinus X

def cornerMP (X : ChiralZorn) : ChiralZorn :=
  peirceComponent zornMinus zornPlus X

def cornerMM (X : ChiralZorn) : ChiralZorn :=
  peirceComponent zornMinus zornMinus X

theorem cornerPP_eq_nPlus (X : ChiralZorn) :
    cornerPP X = X.a • zornPlus := by
  rw [cornerPP, peirce_plus_plus_apply]
  apply ZornMatrix.ext
  · simp [zornPlus, ZornMatrix.smul_a]
  · simp [zornPlus, ZornMatrix.smul_b]
  · funext i; fin_cases i <;> simp [zornPlus, ZornMatrix.smul_x]
  · funext i; fin_cases i <;> simp [zornPlus, ZornMatrix.smul_y]

theorem cornerPM_eq_sigmaPlus_sum (X : ChiralZorn) :
    cornerPM X = ∑ i : Fin 3, X.x i • chiralUpperBasis i := by
  exact colorProject_eq_chiralUpper_sum X

theorem cornerMP_eq_sigmaMinus_sum (X : ChiralZorn) :
    cornerMP X = ∑ i : Fin 3, X.y i • chiralLowerBasis i := by
  exact anticolorProject_eq_chiralLower_sum X

theorem cornerMM_eq_nMinus (X : ChiralZorn) :
    cornerMM X = X.b • zornMinus := by
  rw [cornerMM, peirce_minus_minus_apply]
  apply ZornMatrix.ext
  · simp [zornMinus, ZornMatrix.smul_a]
  · simp [zornMinus, ZornMatrix.smul_b]
  · funext i; fin_cases i <;> simp [zornMinus, ZornMatrix.smul_x]
  · funext i; fin_cases i <;> simp [zornMinus, ZornMatrix.smul_y]

theorem peirce_four_corner_decomposition (X : ChiralZorn) :
    X = cornerPP X + cornerPM X + cornerMP X + cornerMM X := by
  exact zorn_peirce_decomposition X

theorem peirce_decomposition_chiral (X : ChiralZorn) :
    X = X.a • zornPlus +
      (∑ i : Fin 3, X.x i • chiralUpperBasis i) +
      (∑ i : Fin 3, X.y i • chiralLowerBasis i) +
      X.b • zornMinus := by
  have h := peirce_four_corner_decomposition X
  rw [cornerPP_eq_nPlus, cornerPM_eq_sigmaPlus_sum,
    cornerMP_eq_sigmaMinus_sum, cornerMM_eq_nMinus] at h
  exact h

def chiralVectorProject (X : ChiralZorn) : ChiralZorn :=
  cornerPM X + cornerMP X

@[simp] theorem chiralVectorProject_a (X : ChiralZorn) :
    (chiralVectorProject X).a = 0 := by
  change (colorProject X + anticolorProject X).a = 0
  rw [colorProject_apply, anticolorProject_apply, ZornMatrix.add_def]
  simp

@[simp] theorem chiralVectorProject_b (X : ChiralZorn) :
    (chiralVectorProject X).b = 0 := by
  change (colorProject X + anticolorProject X).b = 0
  rw [colorProject_apply, anticolorProject_apply, ZornMatrix.add_def]
  simp

theorem chiralVectorProject_eq_color_add_anticolor (X : ChiralZorn) :
    chiralVectorProject X = colorProject X + anticolorProject X := by
  change cornerPM X + cornerMP X = colorProject X + anticolorProject X
  rfl

theorem chiralVectorProject_apply (X : ChiralZorn) :
    chiralVectorProject X =
      { a := 0, b := 0, x := X.x, y := X.y } := by
  rw [chiralVectorProject_eq_color_add_anticolor,
    colorProject_apply, anticolorProject_apply, ZornMatrix.add_def]
  apply ZornMatrix.ext <;> simp

theorem chiralVectorProject_add (X Y : ChiralZorn) :
    chiralVectorProject (X + Y) = chiralVectorProject X + chiralVectorProject Y := by
  rw [chiralVectorProject_apply, chiralVectorProject_apply, chiralVectorProject_apply,
    ZornMatrix.add_def, ZornMatrix.add_def]
  apply ZornMatrix.ext <;> simp

theorem chiralVectorProject_smul (r : ℚ) (X : ChiralZorn) :
    chiralVectorProject (r • X) = r • chiralVectorProject X := by
  rw [chiralVectorProject_apply, chiralVectorProject_apply]
  apply ZornMatrix.ext
  · simp [ZornMatrix.smul_a]
  · simp [ZornMatrix.smul_b]
  · funext i; simp [ZornMatrix.smul_x]
  · funext i; simp [ZornMatrix.smul_y]

/-- The mixed Peirce sector as a linear endomorphism of the native Zorn carrier. -/
def chiralVectorProjectLinear : ChiralZorn →ₗ[ℚ] ChiralZorn where
  toFun := chiralVectorProject
  map_add' := chiralVectorProject_add
  map_smul' := chiralVectorProject_smul

/-- Clifford soldering on the mixed chiral sector only. -/
def chiralCliffordSolder (X : ChiralZorn) :
    Module.End ℚ (ZornClifford.DiracSpinor16 (R := ℚ)) :=
  ZornClifford.diracGamma (chiralVectorProject X)

theorem chiralCliffordSolder_sq (X : ChiralZorn)
    (Ψ : ZornClifford.DiracSpinor16 (R := ℚ)) :
    chiralCliffordSolder X (chiralCliffordSolder X Ψ) =
      ZornClifford.zornNormFun (chiralVectorProject X) • Ψ := by
  simpa [chiralCliffordSolder] using
    (ZornClifford.diracGamma_sq_apply (R := ℚ) (chiralVectorProject X) Ψ)

/-- The mixed Peirce sector is solders linearly into endomorphisms. -/
def chiralCliffordSolderLinear :
    ChiralZorn →ₗ[ℚ] Module.End ℚ (ZornClifford.DiracSpinor16 (R := ℚ)) :=
  ZornClifford.diracGammaLinear.comp chiralVectorProjectLinear

@[simp] theorem chiralCliffordSolderLinear_apply (X : ChiralZorn) :
    chiralCliffordSolderLinear X = chiralCliffordSolder X := rfl

theorem chiral_peirce_soldering_synthesis (X : ChiralZorn) :
    cornerPP X = X.a • zornPlus ∧
    cornerPM X = ∑ i : Fin 3, X.x i • chiralUpperBasis i ∧
    cornerMP X = ∑ i : Fin 3, X.y i • chiralLowerBasis i ∧
    cornerMM X = X.b • zornMinus ∧
    X = cornerPP X + cornerPM X + cornerMP X + cornerMM X := by
  exact ⟨cornerPP_eq_nPlus X, cornerPM_eq_sigmaPlus_sum X,
    cornerMP_eq_sigmaMinus_sum X, cornerMM_eq_nMinus X,
    peirce_four_corner_decomposition X⟩

end InfoGeometry.Canonical
