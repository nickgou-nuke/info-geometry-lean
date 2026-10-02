import InfoGeometry.Algebra.Zorn.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Canonical.ZornMatrix

def oneZ : ZornMatrix ℚ := { a := 1, b := 1, x := ![0, 0, 0], y := ![0, 0, 0] }
def zeroZ : ZornMatrix ℚ := { a := 0, b := 0, x := ![0, 0, 0], y := ![0, 0, 0] }
def ePlus : ZornMatrix ℚ := { a := 1, b := 0, x := ![0, 0, 0], y := ![0, 0, 0] }
def eMinus : ZornMatrix ℚ := { a := 0, b := 1, x := ![0, 0, 0], y := ![0, 0, 0] }
def up0 : ZornMatrix ℚ := { a := 0, b := 0, x := ![1, 0, 0], y := ![0, 0, 0] }
def down0 : ZornMatrix ℚ := { a := 0, b := 0, x := ![0, 0, 0], y := ![1, 0, 0] }
def J : ZornMatrix ℚ := { a := 0, b := 0, x := ![1, 0, 0], y := ![-1, 0, 0] }
def half (z : ZornMatrix ℚ) : ZornMatrix ℚ := { a := z.a / 2, b := z.b / 2, x := fun i => z.x i / 2, y := fun i => z.y i / 2 }

theorem J_sq : J * J = -oneZ := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [J, oneZ, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem up0_sq : up0 * up0 = zeroZ := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [up0, zeroZ, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem down0_sq : down0 * down0 = zeroZ := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [down0, zeroZ, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem up0_mul_down0 : up0 * down0 = ePlus := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [up0, down0, ePlus, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem down0_mul_up0 : down0 * up0 = eMinus := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [down0, up0, eMinus, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

def alpha : ZornMatrix ℚ := half (J + J * J)
def alpha_dag : ZornMatrix ℚ := half (J - J * J)

theorem alpha_explicit : alpha = { a := -1/2, b := -1/2, x := ![1/2, 0, 0], y := ![-1/2, 0, 0] } := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [alpha, half, J, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem alpha_dag_explicit : alpha_dag = { a := 1/2, b := 1/2, x := ![1/2, 0, 0], y := ![-1/2, 0, 0] } := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [alpha_dag, half, J, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem alpha_sq_eq_half_negJ : alpha * alpha = half (-J) := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [alpha, half, J, InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem alpha_dag_sq_eq_half_J : alpha_dag * alpha_dag = half J := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [alpha_dag, half, J, InfoGeometry.Canonical.ZornMatrix.mul, InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem CAR_anticommutator : alpha * alpha_dag + alpha_dag * alpha = -oneZ := by
  rw [alpha_explicit, alpha_dag_explicit]
  ext <;> (try rename_i i; fin_cases i) <;> simp [mul, dot, cross, oneZ, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem alpha_alpha_dag : alpha * alpha_dag = { a := -1/2, b := -1/2, x := ![0, 0, 0], y := ![0, 0, 0] } := by
  rw [alpha_explicit, alpha_dag_explicit]
  ext <;> (try rename_i i; fin_cases i) <;> simp [mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem alpha_dag_alpha : alpha_dag * alpha = { a := -1/2, b := -1/2, x := ![0, 0, 0], y := ![0, 0, 0] } := by
  rw [alpha_explicit, alpha_dag_explicit]
  ext <;> (try rename_i i; fin_cases i) <;> simp [mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

def up : Fin 3 → ZornMatrix ℚ
  | ⟨0, _⟩ => up0
  | ⟨1, _⟩ => { a := 0, b := 0, x := ![0, 1, 0], y := ![0, 0, 0] }
  | ⟨2, _⟩ => { a := 0, b := 0, x := ![0, 0, 1], y := ![0, 0, 0] }

def down : Fin 3 → ZornMatrix ℚ
  | ⟨0, _⟩ => down0
  | ⟨1, _⟩ => { a := 0, b := 0, x := ![0, 0, 0], y := ![0, 1, 0] }
  | ⟨2, _⟩ => { a := 0, b := 0, x := ![0, 0, 0], y := ![0, 0, 1] }

theorem up_one_mul_down_one : up 1 * down 1 = ePlus := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [up, down, ePlus, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem up_two_mul_down_two : up 2 * down 2 = ePlus := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [up, down, ePlus, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem up_one_mul_down_two : up 1 * down 2 = zeroZ := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [up, down, zeroZ, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem down_one_mul_up_two : down 1 * up 2 = zeroZ := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [up, down, zeroZ, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem down_two_mul_up_two : down 2 * up 2 = eMinus := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [up, down, eMinus, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

theorem down_one_mul_up_one : down 1 * up 1 = eMinus := by
  ext <;> (try rename_i i; fin_cases i) <;> simp [up, down, eMinus, mul, dot, cross, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] <;> try norm_num

def J_color (i : Fin 3) : ZornMatrix ℚ := up i - down i

def alpha_color (i : Fin 3) : ZornMatrix ℚ :=
  half (J_color i + J_color i * J_color i)

def alpha_dag_color (i : Fin 3) : ZornMatrix ℚ :=
  half (J_color i - J_color i * J_color i)

theorem mersenne_M2_eq_color_dim : (2 : ℕ)^2 - 1 = 3 := by norm_num

structure CARResult where
  J_sq : J * J = -oneZ
  up0_nilpotent : up0 * up0 = zeroZ
  down0_nilpotent : down0 * down0 = zeroZ
  up0_down0_ePlus : up0 * down0 = ePlus
  down0_up0_eMinus : down0 * up0 = eMinus
  anticommutator : alpha * alpha_dag + alpha_dag * alpha = -oneZ
  alpha_alpha_dag : alpha * alpha_dag = { a := -1/2, b := -1/2, x := ![0, 0, 0], y := ![0, 0, 0] }
  alpha_dag_alpha : alpha_dag * alpha = { a := -1/2, b := -1/2, x := ![0, 0, 0], y := ![0, 0, 0] }

theorem furey_CAR_complete : CARResult :=
  ⟨J_sq, up0_sq, down0_sq, up0_mul_down0, down0_mul_up0, CAR_anticommutator, alpha_alpha_dag, alpha_dag_alpha⟩

end InfoGeometry.OperatorAlgebra.SplitOctonions.FureyCAR
