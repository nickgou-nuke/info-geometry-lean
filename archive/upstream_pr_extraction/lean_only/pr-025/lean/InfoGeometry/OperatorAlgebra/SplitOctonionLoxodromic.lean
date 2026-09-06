import InfoGeometry.OperatorAlgebra.SplitQuaternionSL2Isomorphism
import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
import InfoGeometry.Canonical.ZornCliffordRepresentation

/-!
# 8D Split-Octonionic Loxodromic Actions

This module formalizes the lifting of SL(2, ℝ) matrix transformations into
8D split-octonionic left-multiplication operators.

1. `embedM2`: Embeds a real 2x2 matrix into the canonical Zorn carrier as a
   split-quaternion subalgebra element.
2. `liftSL2ToSplitOctonion`: Constructs the 8x8 matrix representing the left-multiplication
   operator by the embedded matrix.
3. `liftSL2ToSplitOctonion_one`: Proves that the identity matrix in M₂(ℝ) lifts to
   the identity matrix in M₈(ℝ).

All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
-/

open Matrix
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal

namespace InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic

/-- Embed a real 2x2 matrix into the Zorn matrix carrier. -/
def embedM2 (A : Matrix (Fin 2) (Fin 2) ℝ) : CanonicalZorn :=
  { a := A 0 0, b := A 1 1, x := ![A 0 1, 0, 0], y := ![A 1 0, 0, 0] }

/-- Left-multiplication by a Zorn matrix as a linear map. -/
def zMulLinear (Z : CanonicalZorn) : Module.End ℝ CanonicalZorn :=
  { toFun := fun W => Z * W
    map_add' := fun X Y => mul_add' Z X Y
    map_smul' := fun r X => mul_smul' r Z X }

/-- Left multiplication on the coordinate space `Fin 8 → ℝ`. -/
def leftMulLinearGeneral (Z : CanonicalZorn) : Module.End ℝ (Fin 8 → ℝ) :=
  (coordLE : CanonicalZorn →ₗ[ℝ] (Fin 8 → ℝ)) ∘ₗ
    zMulLinear Z ∘ₗ
    (coordLE.symm : (Fin 8 → ℝ) →ₗ[ℝ] CanonicalZorn)

/-- The 8x8 matrix representing left multiplication by a general Zorn matrix. -/
def leftMulMatrixGeneral (Z : CanonicalZorn) : Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrix' (leftMulLinearGeneral Z)

/-- Lift an SL(2, ℝ) matrix representation into an 8x8 split-octonionic
    left-multiplication matrix. -/
def liftSL2ToSplitOctonion (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  leftMulMatrixGeneral (embedM2 A)

private theorem zorn_one_mul (Z : CanonicalZorn) : 1 * Z = Z := by
  rcases Z with ⟨a, b, x, y⟩
  have h1 : (1 : ZornMatrix ℝ) = { a := 1, b := 1, x := 0, y := 0 } := rfl
  rw [h1]
  apply ZornMatrix.ext
  · simp [mul_def, mul, dot, cross]
  · simp [mul_def, mul, dot, cross]
  · ext i; fin_cases i <;> simp [mul_def, mul, dot, cross]
  · ext i; fin_cases i <;> simp [mul_def, mul, dot, cross]

/-- The lift of the identity matrix is the identity matrix. -/
theorem liftSL2ToSplitOctonion_one :
    liftSL2ToSplitOctonion (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  simp only [liftSL2ToSplitOctonion, leftMulMatrixGeneral, embedM2]
  have h1 : ({ a := (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0,
               b := (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1,
               x := ![(1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1, 0, 0],
               y := ![(1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0, 0, 0] } : CanonicalZorn) = 1 := by
    apply ZornMatrix.ext
    · show (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (1 : CanonicalZorn).a
      rfl
    · show (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (1 : CanonicalZorn).b
      rfl
    · ext i; fin_cases i <;> rfl
    · ext i; fin_cases i <;> rfl
  rw [h1]
  have h2 : leftMulLinearGeneral 1 = 1 := by
    apply LinearMap.ext
    intro v
    change coordLE (1 * coordLE.symm v) = v
    rw [zorn_one_mul]
    exact coordLE.apply_symm_apply v
  rw [h2]
  simp

end InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic
