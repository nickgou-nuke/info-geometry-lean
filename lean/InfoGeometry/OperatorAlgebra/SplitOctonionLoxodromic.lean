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

@[simp] theorem embedM2_zero :
    embedM2 (0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  change embedM2 (0 : Matrix (Fin 2) (Fin 2) ℝ) =
    ({ a := 0, b := 0, x := 0, y := 0 } : CanonicalZorn)
  apply ZornMatrix.ext <;> simp [embedM2]

@[simp] theorem embedM2_add (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    embedM2 (A + B) = embedM2 A + embedM2 B := by
  apply ZornMatrix.ext <;> simp [embedM2]

@[simp] theorem embedM2_smul (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    embedM2 (r • A) = r • embedM2 A := by
  change embedM2 (r • A) =
    ({ a := r * A 0 0, b := r * A 1 1,
       x := r • ![A 0 1, 0, 0], y := r • ![A 1 0, 0, 0] } : CanonicalZorn)
  apply ZornMatrix.ext <;> simp [embedM2]

@[simp] theorem embedM2_one :
    embedM2 (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  change embedM2 (1 : Matrix (Fin 2) (Fin 2) ℝ) =
    ({ a := 1, b := 1, x := 0, y := 0 } : CanonicalZorn)
  apply ZornMatrix.ext <;> simp [embedM2]

/-- The coordinate embedding is multiplicative onto its split-quaternion plane.

This statement is internal to the associative embedded plane.  It does not
assert that left multiplication on the full split-octonion carrier is an
associative representation.
-/
theorem embedM2_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    embedM2 (A * B) = embedM2 A * embedM2 B := by
  apply ZornMatrix.ext
  · simp [embedM2, mul_def, mul, dot, cross, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring
  · simp [embedM2, mul_def, mul, dot, cross, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring
  · ext i
    fin_cases i <;>
      simp [embedM2, mul_def, mul, dot, cross, Matrix.mul_apply,
        Fin.sum_univ_two] <;> ring
  · ext i
    fin_cases i <;>
      simp [embedM2, mul_def, mul, dot, cross, Matrix.mul_apply,
        Fin.sum_univ_two] <;> ring

theorem embedM2_injective : Function.Injective embedM2 := by
  intro A B h
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact congrArg ZornMatrix.a h
  · exact congrFun (congrArg ZornMatrix.x h) 0
  · exact congrFun (congrArg ZornMatrix.y h) 0
  · exact congrArg ZornMatrix.b h

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

/-- Coordinate action of the left-multiplication matrix. -/
theorem leftMulMatrixGeneral_mulVec (Z : CanonicalZorn) (v : Fin 8 → ℝ) :
    (leftMulMatrixGeneral Z).mulVec v =
      coordLE (Z * coordLE.symm v) := by
  simpa [leftMulMatrixGeneral, leftMulLinearGeneral, zMulLinear] using
    (LinearMap.toMatrix'_mulVec (leftMulLinearGeneral Z) v).symm

/-- Lift an SL(2, ℝ) matrix representation into an 8x8 split-octonionic
    left-multiplication matrix. -/
def liftSL2ToSplitOctonion (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  leftMulMatrixGeneral (embedM2 A)

/-- On the embedded split-quaternion plane, the lifted operator realizes
ordinary `2 × 2` matrix multiplication exactly. -/
theorem liftSL2ToSplitOctonion_mulVec_embedM2
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    (liftSL2ToSplitOctonion A).mulVec (coordLE (embedM2 B)) =
      coordLE (embedM2 (A * B)) := by
  rw [liftSL2ToSplitOctonion, leftMulMatrixGeneral_mulVec,
    coordLE.symm_apply_apply, ← embedM2_mul]

/-- Composition of lifted actions is associative on the embedded
split-quaternion plane, even though the ambient Zorn carrier is not
associative. -/
theorem liftSL2ToSplitOctonion_comp_on_embedM2
    (A B C : Matrix (Fin 2) (Fin 2) ℝ) :
    (liftSL2ToSplitOctonion A).mulVec
        ((liftSL2ToSplitOctonion B).mulVec (coordLE (embedM2 C))) =
      (liftSL2ToSplitOctonion (A * B)).mulVec (coordLE (embedM2 C)) := by
  rw [liftSL2ToSplitOctonion_mulVec_embedM2,
    liftSL2ToSplitOctonion_mulVec_embedM2,
    liftSL2ToSplitOctonion_mulVec_embedM2, Matrix.mul_assoc]

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
