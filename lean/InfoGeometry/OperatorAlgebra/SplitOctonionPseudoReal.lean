import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Canonical.ZornSpinor
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Split-octonion pseudo-real 8×8 matrix representation

This module packages left multiplication by an imaginary split octonion as an
explicit `8 × 8` real matrix on the full canonical Zorn carrier.

The matrix is defined on the honest coordinate model
`(a, x₀, x₁, x₂, y₀, y₁, y₂, b) : Fin 8 → ℝ`, so the resulting theorems are
native Mathlib statements about endomorphisms of `Fin 8 → ℝ`.

No `sorry`/`axiom`/`admit`/certificate scaffolding is used.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal

open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix

abbrev CanonicalZorn := InfoGeometry.Canonical.ZornMatrix ℝ

/-- Linear equivalence from `CanonicalZorn` to `Fin 8 → ℝ` with order
`(a, x₀, x₁, x₂, y₀, y₁, y₂, b)`. -/
def coordLE : CanonicalZorn ≃ₗ[ℝ] (Fin 8 → ℝ) :=
  { toFun := fun Z => ![Z.a, Z.x 0, Z.x 1, Z.x 2, Z.y 0, Z.y 1, Z.y 2, Z.b]
    invFun := fun v => { a := v 0, b := v 7, x := ![v 1, v 2, v 3], y := ![v 4, v 5, v 6] }
    map_add' := fun Z W => by
      ext i; fin_cases i <;> rfl
    map_smul' := fun r Z => by
      ext i; fin_cases i <;> rfl
    left_inv := fun Z => by
      rcases Z with ⟨a, b, x, y⟩
      apply ZornMatrix.ext
      · rfl
      · rfl
      · ext i; fin_cases i <;> rfl
      · ext i; fin_cases i <;> rfl
    right_inv := fun v => by
      funext i; fin_cases i <;> rfl }

/-- Left multiplication by an imaginary split octonion, transported to the
coordinate space `Fin 8 → ℝ`. -/
def leftMulLinear (X : Imaginary) : Module.End ℝ (Fin 8 → ℝ) :=
  (coordLE : CanonicalZorn →ₗ[ℝ] (Fin 8 → ℝ)) ∘ₗ
    imaginaryLeftMul X ∘ₗ
    (coordLE.symm : (Fin 8 → ℝ) →ₗ[ℝ] CanonicalZorn)

/-- The pseudo-real `8 × 8` matrix representative of left multiplication by an
imaginary split octonion. -/
def leftMulMatrix (X : Imaginary) : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix' (leftMulLinear X)

@[simp] theorem toLin_leftMulMatrix (X : Imaginary) :
    Matrix.toLin' (leftMulMatrix X) = leftMulLinear X := by
  simp [leftMulMatrix]

@[simp] theorem leftMulMatrix_mulVec (X : Imaginary) (v : Fin 8 → ℝ) :
    Matrix.mulVec (leftMulMatrix X) v = leftMulLinear X v := by
  simp [leftMulMatrix, LinearMap.toMatrix'_mulVec]

/-- Conjugating scalar endomorphisms through `coordLE` does nothing. -/
@[simp] theorem leftMulLinear_algebraMap (r : ℝ) :
    ((coordLE : CanonicalZorn →ₗ[ℝ] (Fin 8 → ℝ)) ∘ₗ
      (algebraMap ℝ (Module.End ℝ CanonicalZorn) r) ∘ₗ
      (coordLE.symm : (Fin 8 → ℝ) →ₗ[ℝ] CanonicalZorn)) =
    algebraMap ℝ (Module.End ℝ (Fin 8 → ℝ)) r := by
  apply LinearMap.ext
  intro v
  ext i
  change coordLE (r • coordLE.symm v) i = (algebraMap ℝ (Module.End ℝ (Fin 8 → ℝ)) r v) i
  rw [map_smul, coordLE.apply_symm_apply]
  rfl

/-- The `8 × 8` matrix of `L_X` satisfies the Clifford square law. -/
theorem leftMulMatrix_sq (X : Imaginary) :
    leftMulMatrix X * leftMulMatrix X =
      (leftCliffordQuadratic X : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul, map_smul, toLin_leftMulMatrix]
  apply LinearMap.ext
  intro v
  ext i
  simp only [leftMulLinear, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply, Matrix.toLin'_one, LinearMap.smul_apply, LinearMap.id_apply]
  change coordLE (imaginaryLeftMul X (imaginaryLeftMul X (coordLE.symm v))) i = (leftCliffordQuadratic X • v) i
  rw [← Module.End.mul_apply, imaginaryLeftMul_sq X]
  change coordLE (leftCliffordQuadratic X • coordLE.symm v) i = _
  rw [map_smul, coordLE.apply_symm_apply]

/-- The matrix anticommutator is the polar form of the Clifford quadratic. -/
theorem leftMulMatrix_anticommutator (X Y : Imaginary) :
    leftMulMatrix X * leftMulMatrix Y + leftMulMatrix Y * leftMulMatrix X =
      (QuadraticMap.polar leftCliffordQuadratic X Y : ℝ) •
        (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  apply Matrix.toLin'.injective
  simp only [map_add, Matrix.toLin'_mul, map_smul, toLin_leftMulMatrix]
  apply LinearMap.ext
  intro v
  ext i
  simp only [leftMulLinear, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply, Matrix.toLin'_one, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.add_apply]
  change (coordLE (imaginaryLeftMul X (imaginaryLeftMul Y (coordLE.symm v))) +
    coordLE (imaginaryLeftMul Y (imaginaryLeftMul X (coordLE.symm v)))) i =
    (QuadraticMap.polar leftCliffordQuadratic X Y • v) i
  rw [← map_add]
  change coordLE ((imaginaryLeftMul X * imaginaryLeftMul Y + imaginaryLeftMul Y * imaginaryLeftMul X) (coordLE.symm v)) i = _
  rw [imaginaryLeftMul_anticommutator X Y]
  change coordLE (QuadraticMap.polar leftCliffordQuadratic X Y • coordLE.symm v) i = _
  rw [map_smul, coordLE.apply_symm_apply]

private theorem zorn_mul_one (z : CanonicalZorn) : z * 1 = z := by
  rcases z with ⟨a, b, x, y⟩
  have h1 : (1 : ZornMatrix ℝ) = { a := 1, b := 1, x := 0, y := 0 } := rfl
  rw [h1]
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross]
  · simp [mul_def, mul, dot, cross]
  · ext i
    fin_cases i <;> simp [mul_def, mul, dot, cross]
  · ext i
    fin_cases i <;> simp [mul_def, mul, dot, cross]

/-- The matrix representation is faithful. -/
theorem leftMulMatrixLinear_injective :
    Function.Injective (fun X : Imaginary => leftMulMatrix X) := by
  intro X Y hXY
  have hlin : leftMulLinear X = leftMulLinear Y := by
    apply LinearMap.toMatrix'.injective
    simpa [leftMulMatrix] using hXY
  have hone := congrArg (fun f => f (coordLE (1 : CanonicalZorn))) hlin
  have hcanon : X.1 = Y.1 := by
    apply coordLE.injective
    simp only [leftMulLinear, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply] at hone
    change coordLE (X.1 * 1) = coordLE (Y.1 * 1) at hone
    rw [zorn_mul_one, zorn_mul_one] at hone
    exact hone
  exact Subtype.ext hcanon

/-- Honest determinant consequence of the Clifford square law:
`det(L_X)^2 = Q(X)^8`.

This is the exact statement forced by `L_X^2 = Q(X) I` in dimension `8`. -/
theorem leftMulMatrix_det (X : Imaginary) :
    Matrix.det (leftMulMatrix X) ^ 2 = (leftCliffordQuadratic X : ℝ) ^ 8 := by
  have h := congrArg Matrix.det (leftMulMatrix_sq X)
  simpa [pow_two, Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] using h

end InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
