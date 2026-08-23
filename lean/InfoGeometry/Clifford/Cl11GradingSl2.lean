import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Canonical.SplitQuaternionMatrixModel
import InfoGeometry.Physics.ParabolicClock
import Mathlib.Tactic

/-!
# Native `sl₂(ℝ)` grading triple inside `Cl(1,1)`

The repository already owns the algebra equivalence

`CliffordAlgebra q11 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ`

in `Cl11Matrix`.  This file uses that owner rather than introducing another
Clifford or split-quaternion carrier.  It identifies the parabolic clock with
the positive nilpotent matrix unit, completes it to the standard `sl₂` triple,
and transports the three generators back to the native Clifford algebra.

No exceptional Lie algebra is asserted here.  This is only the exact
`Cl(1,1)` grading-axis realization needed by later five-graded constructions.
-/

open scoped Matrix

namespace InfoGeometry.Clifford.Cl11GradingSl2

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Canonical.SplitQuaternionMatrixModel

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Cl11 := CliffordAlgebra q11

/-- Positive nilpotent root generator.  This is definitionally the repository
parabolic clock matrix. -/
def E : Mat2 := InfoGeometry.Physics.K (R := ℝ)

/-- Negative nilpotent root generator. -/
def F : Mat2 := !![(0 : ℝ), 0; 1, 0]

/-- Cartan grading generator. -/
def H : Mat2 := !![(1 : ℝ), 0; 0, -1]

@[simp] theorem E_sq : E * E = 0 := by
  exact InfoGeometry.Physics.K_sq_eq_zero (R := ℝ)

@[simp] theorem F_sq : F * F = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [F, Matrix.mul_apply, Fin.sum_univ_two]

/-- The positive grading generator is exactly the existing split-quaternion
null hop. -/
theorem E_eq_splitNilpotentPlus : E = splitNilpotentPlus := by
  rw [splitNilpotents_explicit]
  rfl

/-- The negative grading generator is exactly the opposite split-quaternion
null hop. -/
theorem F_eq_splitNilpotentMinus : F = splitNilpotentMinus := by
  rw [splitNilpotents_explicit]
  rfl

/-- `[H,E] = 2E`. -/
theorem bracket_H_E : ⁅H, E⁆ = (2 : ℝ) • E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Ring.lie_def, H, E, InfoGeometry.Physics.K,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- `[H,F] = -2F`. -/
theorem bracket_H_F : ⁅H, F⁆ = (-2 : ℝ) • F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Ring.lie_def, H, F,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- `[E,F] = H`. -/
theorem bracket_E_F : ⁅E, F⁆ = H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Ring.lie_def, H, E, F, InfoGeometry.Physics.K,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The complete standard `sl₂(ℝ)` matrix triple used by the grading axis. -/
theorem parabolicSL2Triple :
    ⁅H, E⁆ = (2 : ℝ) • E ∧
      ⁅H, F⁆ = (-2 : ℝ) • F ∧
        ⁅E, F⁆ = H :=
  ⟨bracket_H_E, bracket_H_F, bracket_E_F⟩

/-- The repository parabolic clock is literally the raising generator. -/
@[simp] theorem parabolicClock_eq_E :
    InfoGeometry.Physics.K (R := ℝ) = E := rfl

/-! ## Transport to the native Clifford carrier -/

/-- Positive root generator transported to native `Cl(1,1)`. -/
def clE : Cl11 := cl11EquivMat.symm E

/-- Negative root generator transported to native `Cl(1,1)`. -/
def clF : Cl11 := cl11EquivMat.symm F

/-- Cartan generator transported to native `Cl(1,1)`. -/
def clH : Cl11 := cl11EquivMat.symm H

@[simp] theorem cl11EquivMat_clE : cl11EquivMat clE = E :=
  cl11EquivMat.apply_symm_apply E

@[simp] theorem cl11EquivMat_clF : cl11EquivMat clF = F :=
  cl11EquivMat.apply_symm_apply F

@[simp] theorem cl11EquivMat_clH : cl11EquivMat clH = H :=
  cl11EquivMat.apply_symm_apply H

/-- Native Clifford relation `[clH,clE] = 2 clE`. -/
theorem cl_bracket_H_E : ⁅clH, clE⁆ = (2 : ℝ) • clE := by
  apply cl11EquivMat.injective
  simpa [Ring.lie_def] using bracket_H_E

/-- Native Clifford relation `[clH,clF] = -2 clF`. -/
theorem cl_bracket_H_F : ⁅clH, clF⁆ = (-2 : ℝ) • clF := by
  apply cl11EquivMat.injective
  simpa [Ring.lie_def] using bracket_H_F

/-- Native Clifford relation `[clE,clF] = clH`. -/
theorem cl_bracket_E_F : ⁅clE, clF⁆ = clH := by
  apply cl11EquivMat.injective
  simpa [Ring.lie_def] using bracket_E_F

/-- The standard grading `sl₂` triple exists inside the native Clifford
algebra, not merely in an external matrix witness. -/
theorem cl11ParabolicSL2Triple :
    ⁅clH, clE⁆ = (2 : ℝ) • clE ∧
      ⁅clH, clF⁆ = (-2 : ℝ) • clF ∧
        ⁅clE, clF⁆ = clH :=
  ⟨cl_bracket_H_E, cl_bracket_H_F, cl_bracket_E_F⟩

/-- Under the established Clifford/matrix equivalence, the native positive
root generator is exactly the parabolic clock. -/
theorem clE_maps_to_parabolicClock :
    cl11EquivMat clE = InfoGeometry.Physics.K (R := ℝ) := by
  rfl

end

end InfoGeometry.Clifford.Cl11GradingSl2
