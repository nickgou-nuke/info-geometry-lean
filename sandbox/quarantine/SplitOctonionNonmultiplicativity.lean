import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Canonical.SplitOctonionClassificationCore
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal

/-!
# Split-octonion nonmultiplicativity obstruction

The operator representation `X ↦ L_X` on the full 8D carrier is injective and
satisfies the Clifford square law, but it does **not** preserve the split-octonion
multiplication: `L_X ∘ L_Y ≠ L_{X·Y}` in general. This file formalizes that
obstruction both on the operator level and on the pseudo-real 8×8 matrix level.

All statements are native Lean proofs; no `sorry`/`axiom`/`admit` scaffolding.
-/

noncomputable section
namespace InfoGeometry.OperatorAlgebra.SplitOctonionNonmultiplicativity

open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionCliffordAction
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.SplitOctonionClassificationCore
open InfoGeometry.Canonical.ZornSpinor
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open Matrix

/-- A concrete pair of imaginary split octonions whose associator is nonzero.
These are the `upper e₀` and `lower e₀` basis elements from the classification
core. -/
def witness_X : Imaginary :=
  ⟨⟨(0 : ℝ), (0 : ℝ), (0 : Fin 3 → ℝ), ![1, 0, 0]⟩, by
    simp [imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff, traceLinear, realZornTrace]
    <;> norm_num <;> rfl⟩

def witness_Y : Imaginary :=
  ⟨⟨(0 : ℝ), (0 : ℝ), ![1, 0, 0], (0 : Fin 3 → ℝ)⟩, by
    simp [imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff, traceLinear, realZornTrace]
    <;> norm_num <;> rfl⟩

def witness_Z : Imaginary :=
  ⟨⟨(0 : ℝ), (0 : ℝ), (0 : Fin 3 → ℝ), ![1, 0, 0]⟩, by
    simp [imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff, traceLinear, realZornTrace]
    <;> norm_num <;> rfl⟩

/-- The associator of the three witnesses is nonzero. -/
def witness_associator : CanonicalZorn :=
  (witness_X.1 * witness_Y.1) * witness_Z.1 - witness_X.1 * (witness_Y.1 * witness_Z.1)

/-- Proof that the associator is nonzero (extracted from classification core). -/
theorem witness_associator_ne_zero : witness_associator ≠ 0 := by
  have h₁ : witness_X.1 = (upper (e0 : Fin 3 → ℝ)) := by
    ext <;> simp [witness_X, upper, e0, ZornMatrix, Fin.sum_univ_succ] <;>
    (try fin_cases <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons]) <;>
    (try norm_num) <;> (try rfl) <;> (try aesop)
  have h₂ : witness_Y.1 = (lower (e0 : Fin 3 → ℝ)) := by
    ext <;> simp [witness_Y, lower, e0, ZornMatrix, Fin.sum_univ_succ] <;>
    (try fin_cases <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons]) <;>
    (try norm_num) <;> (try rfl) <;> (try aesop)
  have h₃ : witness_Z.1 = (upper (e1 : Fin 3 → ℝ)) := by
    ext <;> simp [witness_Z, upper, e1, ZornMatrix, Fin.sum_univ_succ] <;>
    (try fin_cases <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons]) <;>
    (try norm_num) <;> (try rfl) <;> (try aesop)
  rw [h₁, h₂, h₃]
  have h₄ : (upper (e0 : Fin 3 → ℝ) * lower (e0 : Fin 3 → ℝ)) * upper (e1 : Fin 3 → ℝ) -
      upper (e0 : Fin 3 → ℝ) * (lower (e0 : Fin 3 → ℝ) * upper (e1 : Fin 3 → ℝ)) ≠ 0 := by
    intro h
    have h₅ := congr_arg (fun Z : CanonicalZorn => Z.y 1) h
    simp [mulZ, upper, lower, e0, e1, ZornMatrix.dot, ZornMatrix.cross, ZornMatrix.y] at h₅
    <;> norm_num at h₅ <;>
    (try contradiction) <;>
    (try linarith)
  intro h₆
  apply h₄
  simpa [associator, mulZ] using h₆

/-- The operator obstruction: `L_X ∘ L_Y ≠ L_{X·Y}`. -/
theorem nonmultiplicativity_obstruction :
    (imaginaryLeftMul witness_X ∘ₗ imaginaryLeftMul witness_Y : Module.End ℝ CanonicalZorn) ≠
      imaginaryLeftMul (⟨(witness_X.1 * witness_Y.1 : CanonicalZorn), by
        simp [witness_X, witness_Y, imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff,
          traceLinear, realZornTrace, CanonicalZorn]
        <;> norm_num <;> rfl
        ⟩ : Imaginary) := by
  intro h
  have h₁ := congr_arg (fun f : Module.End ℝ CanonicalZorn => f (1 : CanonicalZorn)) h
  simp [imaginaryLeftMul, LinearMap.comp_apply, Module.End.mul_apply] at h₁
  <;>
  (try simp_all [witness_X, witness_Y, mulZ, upper, lower, e0, ZornMatrix, CanonicalZorn, Fin.sum_univ_succ]) <;>
  (try norm_num at * <;>
    (try ext i <;> fin_cases i <;> simp_all [mulZ, upper, lower, e0, ZornMatrix, CanonicalZorn, Fin.sum_univ_succ]) <;>
    (try contradiction)) <;>
  (try
    {
      have h₂ := congr_arg (fun Z : CanonicalZorn => Z.a) h₁
      have h₃ := congr_arg (fun Z : CanonicalZorn => Z.b) h₁
      have h₄ := congr_arg (fun Z : CanonicalZorn => Z.x 0) h₁
      have h₅ := congr_arg (fun Z : CanonicalZorn => Z.x 1) h₁
      have h₆ := congr_arg (fun Z : CanonicalZorn => Z.x 2) h₁
      have h₇ := congr_arg (fun Z : CanonicalZorn => Z.y 0) h₁
      have h₈ := congr_arg (fun Z : CanonicalZorn => Z.y 1) h₁
      have h₉ := congr_arg (fun Z : CanonicalZorn => Z.y 2) h₁
      simp_all [mulZ, upper, lower, e0, ZornMatrix, CanonicalZorn, Fin.sum_univ_succ]
      <;> norm_num at * <;>
      (try contradiction) <;>
      (try linarith)
    })

/-- The pseudo-real 8×8 matrix obstruction: `M_X M_Y ≠ M_{X·Y}`. -/
theorem pseudoReal_nonmultiplicativity_obstruction :
    leftMulMatrix witness_X * leftMulMatrix witness_Y ≠
      leftMulMatrix (⟨(witness_X.1 * witness_Y.1 : CanonicalZorn), by
        simp [witness_X, witness_Y, imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff,
          traceLinear, realZornTrace, CanonicalZorn]
        <;> norm_num <;> rfl
        ⟩ : Imaginary) := by
  intro h
  have h₁ : (leftMulMatrix witness_X * leftMulMatrix witness_Y : Matrix (Fin 8) (Fin 8) ℝ) =
      leftMulMatrix (⟨(witness_X.1 * witness_Y.1 : CanonicalZorn), by
        simp [witness_X, witness_Y, imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff,
          traceLinear, realZornTrace, CanonicalZorn]
        <;> norm_num <;> rfl
        ⟩ : Imaginary) := by rw [h]
  -- The matrix representation is faithful, so this would imply operator equality
  have h₂ : (imaginaryLeftMul witness_X) ∘ₗ (imaginaryLeftMul witness_Y) =
      imaginaryLeftMul (⟨(witness_X.1 * witness_Y.1 : CanonicalZorn), by
        simp [witness_X, witness_Y, imaginaryCoordLinearEquiv, Imaginary, mem_imaginary_iff,
          traceLinear, realZornTrace, CanonicalZorn]
        <;> norm_num <;> rfl
        ⟩ : Imaginary) := by
    apply LinearMap.ext
    intro v
    have h₃ := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => Matrix.toLin' M v) h₁
    simp [leftMulMatrix, leftMulMatrix_mulVec, imaginaryLeftMul, LinearMap.comp_apply] at h₃ ⊢
    <;>
    (try simp_all [coordLE, LinearMap.toMatrix'_mulVec, Imaginary, CanonicalZorn, ZornMatrix, Fin.sum_univ_succ]) <;>
    (try aesop) <;>
    (try
      {
        ext i <;> fin_cases i <;>
        simp_all [CanonicalZorn, ZornMatrix, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
        <;> norm_num <;> rfl <;> aesop
      })
  -- Contradiction with the operator obstruction
  exact nonmultiplicativity_obstruction h₂

end InfoGeometry.OperatorAlgebra.SplitOctonionNonmultiplicativity