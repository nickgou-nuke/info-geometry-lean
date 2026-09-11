import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionClassificationCore
import InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import Mathlib.Data.Matrix.Basic

/-!
# Split-octonion nonmultiplicativity obstruction

The operator representation `X ↦ L_X` on the full 8D carrier is injective and
satisfies the Clifford square law, but it does **not** preserve the split-octonion
multiplication: `L_X ∘ L_Y ≠ L_{X·Y}` in general. This file formalizes that
obstruction both on the operator level and on the pseudo-real 8×8 matrix level.

All statements are native Lean proofs; no placeholder scaffolding.
-/

noncomputable section
namespace InfoGeometry.OperatorAlgebra.SplitOctonionNonmultiplicativity

open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionClassificationCore
open InfoGeometry.Canonical.SplitOctonionClassificationCore.ZornMatrix
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open Matrix



/-- The associator of the three examples is nonzero. -/
def ex_associator : SplitOctonionPseudoReal.CanonicalZorn :=
  (ex_X.1 * ex_Y.1) * ex_Z.1 - ex_X.1 * (ex_Y.1 * ex_Z.1)

/-- Proof that the associator is nonzero. Evaluated directly on the concrete matrices. -/
theorem ex_associator_ne_zero : ex_associator ≠ 0 := by
  intro h
  have h_comp := congr_arg (fun Z : SplitOctonionPseudoReal.CanonicalZorn => Z.a) h
  simp [ex_associator, ex_X, ex_Y, ex_Z, mul, dot, cross] at h_comp

/-- The operator obstruction: `L_X ∘ L_Y ≠ L_{X·Y}`. -/
theorem nonmultiplicativity_obstruction :
    (imaginaryLeftMul ex_X ∘ₗ imaginaryLeftMul ex_Y : Module.End ℝ SplitOctonionPseudoReal.CanonicalZorn) ≠
      imaginaryLeftMul (⟨(ex_X.1 * ex_Y.1 : SplitOctonionPseudoReal.CanonicalZorn), by
        simp [ex_X, ex_Y, realZornTrace, mul, dot, cross]
        ⟩ : Imaginary) := by
  intro h
  have h₁ := congr_arg (fun f : Module.End ℝ SplitOctonionPseudoReal.CanonicalZorn => f ex_Z.1) h
  simp [imaginaryLeftMul, LinearMap.comp_apply] at h₁
  have h₂ : ex_associator = 0 := by
    change (ex_X.1 * ex_Y.1) * ex_Z.1 - ex_X.1 * (ex_Y.1 * ex_Z.1) = 0
    simp only [mul_def]
    rw [← h₁]
    simp
  exact ex_associator_ne_zero h₂

/-- The pseudo-real 8×8 matrix obstruction: `M_X M_Y ≠ M_{X·Y}`. -/
theorem pseudoReal_nonmultiplicativity_obstruction :
    leftMulMatrix ex_X * leftMulMatrix ex_Y ≠
      leftMulMatrix (⟨(ex_X.1 * ex_Y.1 : SplitOctonionPseudoReal.CanonicalZorn), by
        simp [ex_X, ex_Y, realZornTrace, mul, dot, cross]
        ⟩ : Imaginary) := by
  intro h
  have h₁ : (leftMulMatrix ex_X * leftMulMatrix ex_Y : Matrix (Fin 8) (Fin 8) ℝ) =
      leftMulMatrix (⟨(ex_X.1 * ex_Y.1 : SplitOctonionPseudoReal.CanonicalZorn), by
        simp [ex_X, ex_Y, realZornTrace, mul, dot, cross]
        ⟩ : Imaginary) := h
  -- The matrix representation is faithful (leftMulMatrixLinear_injective), so this
  -- would imply operator equality
  have h₂ : (imaginaryLeftMul ex_X) ∘ₗ (imaginaryLeftMul ex_Y) =
      imaginaryLeftMul (⟨(ex_X.1 * ex_Y.1 : SplitOctonionPseudoReal.CanonicalZorn), by
        simp [ex_X, ex_Y, realZornTrace, mul, dot, cross]
        ⟩ : Imaginary) := by
    apply LinearMap.ext
    intro v
    have h₃ := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => Matrix.toLin' M (coordLE v)) h₁
    simp [leftMulLinear, toLin_leftMulMatrix] at h₃
    exact h₃
  -- Contradiction with the operator obstruction
  exact nonmultiplicativity_obstruction h₂

end InfoGeometry.OperatorAlgebra.SplitOctonionNonmultiplicativity