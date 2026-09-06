import InfoGeometry.Krein.DoubledSpace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
set_option linter.unusedSectionVars false

/-!
# DoubledSpaceMatrix

Matrix-coordinate view for `DoubledSpace`.
-/

namespace InfoGeometry.Krein

section MatrixView

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Column-matrix view of doubled states. -/
abbrev DoubledColumn (E : Type*) := Matrix (Fin 2) (Fin 1) E

/-- Convert a doubled state to a `2 × 1` column matrix. -/
noncomputable def toDoubledColumn (u : DoubledSpace E) : DoubledColumn E :=
  fun i _ => if _h : i = 0 then WithLp.fst u else WithLp.snd u

/-- Convert a `2 × 1` column matrix to a doubled state. -/
noncomputable def ofDoubledColumn (M : DoubledColumn E) : DoubledSpace E :=
  to_doubled (M 0 0) (M 1 0)

@[simp] lemma ofDoubledColumn_toDoubledColumn (u : DoubledSpace E) :
    ofDoubledColumn (toDoubledColumn u) = u := by
  apply DoubledSpace.ext
  · simp [ofDoubledColumn, toDoubledColumn]
  · simp [ofDoubledColumn, toDoubledColumn]

@[simp] lemma toDoubledColumn_ofDoubledColumn (M : DoubledColumn E) :
    toDoubledColumn (ofDoubledColumn M) = M := by
  ext i j
  fin_cases i
  · fin_cases j
    simp [toDoubledColumn, ofDoubledColumn]
  · fin_cases j
    simp [toDoubledColumn, ofDoubledColumn]

end MatrixView

end InfoGeometry.Krein
