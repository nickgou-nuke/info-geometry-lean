import InfoGeometry.Canonical.SplitOctonionQuaternionPolar
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Quaternion

open scoped Quaternion
namespace SplitOctonion

/-- The split/chiral axis operator on SplitOctonions.
    Defined as the sheet exchange (A, B) ↦ (B, A). -/
def Gamma_sheet (x : SplitOctonion) : SplitOctonion :=
  ⟨x.b, x.a⟩

/-- The sheet reflection operator on SplitOctonions.
    Defined as (A, B) ↦ (A, -B). -/
def J_sheet (x : SplitOctonion) : SplitOctonion :=
  ⟨x.a, -x.b⟩

lemma Gamma_sheet_sq (x : SplitOctonion) :
    Gamma_sheet (Gamma_sheet x) = x := by
  ext <;> rfl

lemma J_sheet_sq (x : SplitOctonion) :
    J_sheet (J_sheet x) = x := by
  ext <;> simp [J_sheet]

lemma J_sheet_Gamma_sheet_anticomm (x : SplitOctonion) :
    J_sheet (Gamma_sheet x) = - Gamma_sheet (J_sheet x) := by
  ext <;> simp [J_sheet, Gamma_sheet]

/-- The circular/phase axis operator. -/
def K_sheet (x : SplitOctonion) : SplitOctonion :=
  J_sheet (Gamma_sheet x)

lemma K_sheet_sq (x : SplitOctonion) :
    K_sheet (K_sheet x) = - x := by
  ext <;> simp [K_sheet, J_sheet, Gamma_sheet]

end SplitOctonion
