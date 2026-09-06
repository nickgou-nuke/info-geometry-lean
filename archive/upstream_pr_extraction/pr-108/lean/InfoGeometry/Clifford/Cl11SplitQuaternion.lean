import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import InfoGeometry.Clifford.Cl11SheetDiracMatrices

namespace InfoGeometry.Clifford.SplitQuaternion

open Matrix
open InfoGeometry.Clifford

variable {B : Type*} [CommRing B]

/-- A split quaternion represented in the standard Cl(1,1) basis.
q = a • I + b • Γ + c • K + d • J
where Γ² = 1, K² = -1, ΓK = J. -/
def splitQuaternion (a b c d : B) : Matrix (Fin 2) (Fin 2) B :=
  a • I_mat + b • Gamma_mat + c • K_mat + d • J_mat

lemma splitQuaternion_apply (a b c d : B) :
    splitQuaternion a b c d = !![a + b, c + d; -c + d, a - b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [splitQuaternion, I_mat, Gamma_mat, K_mat, J_mat]
  all_goals { try ring }

/-- Clifford conjugation on the split quaternions corresponds to the adjugate matrix. -/
lemma cliffordConjugation_eq_adjugate (a b c d : B) :
    splitQuaternion a (-b) (-c) (-d) = Matrix.adjugate (splitQuaternion a b c d) := by
  rw [splitQuaternion_apply, splitQuaternion_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]
  all_goals { try ring }

/-- The quadratic form q * q_bar is a^2 - b^2 + c^2 - d^2. -/
lemma mul_cliffordConjugation (a b c d : B) :
    splitQuaternion a b c d * splitQuaternion a (-b) (-c) (-d) =
      (a^2 - b^2 + c^2 - d^2) • I_mat := by
  rw [cliffordConjugation_eq_adjugate]
  rw [Matrix.mul_adjugate]
  have h_det : Matrix.det (splitQuaternion a b c d) = a^2 - b^2 + c^2 - d^2 := by
    rw [splitQuaternion_apply]
    simp [Matrix.det_fin_two]
    ring
  rw [h_det]
  have h_one : (1 : Matrix (Fin 2) (Fin 2) B) = I_mat := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h_one]

end InfoGeometry.Clifford.SplitQuaternion
