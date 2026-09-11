import InfoGeometry.Canonical.TwoSheetThreeColorWeyl
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Split-quaternion relations on the six-state sheet carrier

The two sheet operators are kept as concrete matrices.  This owner proves
their split-quaternion relations and the ordinary quaternionic relations
obtained after multiplication by the scalar complex unit.
-/

open scoped Matrix
noncomputable section

namespace InfoGeometry.Canonical.SheetSplitQuaternionic

open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

abbrev Carrier := Mat23C

def P : Carrier := sixParity
def Q : Carrier := sixSheetExchange
def R : Carrier := P * Q

theorem P_sq : P * P = 1 := by
  change sixParity * sixParity = 1
  simpa [pow_two] using sixParity_squared

theorem Q_sq : Q * Q = 1 := by
  change sixSheetExchange * sixSheetExchange = 1
  simpa [pow_two] using sixSheetExchange_involutive

theorem sheet_parity_exchange_anticommutes :
    Q * P = -(P * Q) := by
  rw [P, Q, sixParity, sixSheetExchange,
    kronecker_mul, kronecker_mul]
  have h : sheetExchange * sheetParity =
      -(sheetParity * sheetExchange) := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [sheetExchange, sheetParity, uPlus, uMinus,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [h]
  have hk (A : Mat2C) :
      Matrix.kronecker (-A) (1 : Mat3C) =
        -Matrix.kronecker A (1 : Mat3C) := by
    ext i j
    simp [Matrix.kronecker]
  simpa using hk (sheetParity * sheetExchange)

theorem R_sq : R * R = -1 := by
  calc
    R * R = (P * Q) * (P * Q) := rfl
    _ = P * (Q * P) * Q := by noncomm_ring
    _ = P * (-(P * Q)) * Q := by
      rw [sheet_parity_exchange_anticommutes]
    _ = -((P * P) * (Q * Q)) := by noncomm_ring
    _ = -1 := by rw [P_sq, Q_sq]; simp

theorem split_quaternion_relations :
    P * P = 1 ∧ Q * Q = 1 ∧
      P * Q = R ∧ Q * R = -P ∧ R * P = -Q := by
  refine ⟨P_sq, Q_sq, rfl, ?_, ?_⟩
  · dsimp [R]
    calc
      Q * (P * Q) = (Q * P) * Q := by simp [mul_assoc]
      _ = (-(P * Q)) * Q := by rw [sheet_parity_exchange_anticommutes]
      _ = -(P * (Q * Q)) := by noncomm_ring
      _ = -P := by rw [Q_sq]; simp
  · dsimp [R]
    calc
      P * Q * P = P * (Q * P) := by simp [mul_assoc]
      _ = P * (-(P * Q)) := by rw [sheet_parity_exchange_anticommutes]
      _ = -((P * P) * Q) := by noncomm_ring
      _ = -Q := by rw [P_sq]; simp

end InfoGeometry.Canonical.SheetSplitQuaternionic
