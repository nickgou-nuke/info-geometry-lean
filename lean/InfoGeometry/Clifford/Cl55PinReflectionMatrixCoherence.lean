import InfoGeometry.Clifford.Cl55CoordinateReflectionMatrixBridge
import InfoGeometry.Clifford.Cl55WittPinAction

/-!
# Native Pin reflection and integer matrix coherence

The native Clifford owner identifies the negative Witt Pin generators with
the quadratic reflections on `V55`.  The coordinate owner identifies those
same reflections with the scalar-extended integer matrices.  This file is the
resulting commuting readout; it does not identify the integer matrices with
Clifford algebra elements or claim surjectivity of the Pin action.
-/

namespace InfoGeometry.Clifford.Clifford55

open InfoGeometry.OperatorAlgebra.FullPin55MatrixLaws
open InfoGeometry.Clifford.Cl55IntegerRealMatrixBridge

theorem v55Flatten_pinTwistedAction_f_neg_matrix
    (i : Fin 5) (x : V55) :
    v55Flatten (pinTwistedAction (fNegPin i) x) =
      (intMatrixToReal (pinReflect ⟨i.val + 5, by omega⟩)).mulVec
        (v55Flatten x) := by
  rw [pinTwistedAction_f_neg_eq_negativeReflection]
  exact v55Flatten_negativeReflection_matrix i x

theorem v55Flatten_globalSheetPin_matrix (x : V55) :
    v55Flatten (pinTwistedAction globalSheetPin x) =
      (intMatrixToReal
        (pinReflect 5 * pinReflect 6 * pinReflect 7 * pinReflect 8 * pinReflect 9)).mulVec
        (v55Flatten x) := by
  rw [pinTwistedAction_globalSheetPin_eq_globalSheetReflection]
  rw [intMatrixToReal_mul, intMatrixToReal_mul,
    intMatrixToReal_mul, intMatrixToReal_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [pinReflectReal_mulVec, pinReflectReal_mulVec,
    pinReflectReal_mulVec, pinReflectReal_mulVec,
    pinReflectReal_mulVec]
  ext k
  fin_cases k <;>
    simp [v55Flatten, globalSheetReflectionLinearEquiv, globalSheetReflection]

theorem v55Flatten_globalSheetPin_matrix_isO55 :
    IsO55Real
  (intMatrixToReal
        (pinReflect 5 * pinReflect 6 * pinReflect 7 * pinReflect 8 * pinReflect 9)) := by
  apply intMatrixToReal_isO55
  have h₅₆ := IsO55_mul (pinReflect_all_o55 5) (pinReflect_all_o55 6)
  have h₅₆₇ := IsO55_mul h₅₆ (pinReflect_all_o55 7)
  have h₅₆₇₈ := IsO55_mul h₅₆₇ (pinReflect_all_o55 8)
  exact IsO55_mul h₅₆₇₈ (pinReflect_all_o55 9)

end InfoGeometry.Clifford.Clifford55
