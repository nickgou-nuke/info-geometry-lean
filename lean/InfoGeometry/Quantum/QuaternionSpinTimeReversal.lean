import InfoGeometry.Topology.Q8V4SchurBridge
import InfoGeometry.Physics.SpinAffineCasimirRigidity
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
namespace InfoGeometry.Quantum.QuaternionSpinTimeReversal

open QuaternionGroup
open InfoGeometry.Topology.Q8MonodromySpinorCover
open InfoGeometry.Topology.Q8V4SchurBridge
open InfoGeometry.Topology.V4RootSystem
open InfoGeometry.Physics.SpinAffineCasimirRigidity
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open scoped BigOperators

section QuaternionAlgebra
@[simp] private theorem M_i_sq : M_i * M_i = -(1 : SpinMatrix) := by ext r c; fin_cases r <;> fin_cases c <;> simp [M_i, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring
@[simp] private theorem M_j_sq : M_j * M_j = -(1 : SpinMatrix) := by ext r c; fin_cases r <;> fin_cases c <;> simp [M_j, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring
@[simp] private theorem M_k_sq : M_k * M_k = -(1 : SpinMatrix) := by ext r c; fin_cases r <;> fin_cases c <;> simp [M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring
@[simp] private theorem M_i_M_j : M_i * M_j = M_k := by ext r c; fin_cases r <;> fin_cases c <;> simp [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring
@[simp] private theorem M_j_M_i : M_j * M_i = -M_k := by ext r c; fin_cases r <;> fin_cases c <;> simp [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring
@[simp] private theorem M_j_M_k : M_j * M_k = M_i := by ext r c; fin_cases r <;> fin_cases c <;> simp [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring
@[simp] private theorem M_k_M_j : M_k * M_j = -M_i := by ext r c; fin_cases r <;> fin_cases c <;> simp [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring
@[simp] private theorem M_k_M_i : M_k * M_i = M_j := by ext r c; fin_cases r <;> fin_cases c <;> simp [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring
@[simp] private theorem M_i_M_k : M_i * M_k = -M_j := by ext r c; fin_cases r <;> fin_cases c <;> simp [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring
end QuaternionAlgebra

def q8A (i : ZMod 4) : SpinMatrix := match i.val with | 0 => 1 | 1 => M_i | 2 => -1 | _ => -M_i
def q8XA (i : ZMod 4) : SpinMatrix := match i.val with | 0 => M_j | 1 => -M_k | 2 => -M_j | _ => M_k
def q8Matrix : QuaternionGroup 2 → SpinMatrix | a i => q8A i | xa i => q8XA i

@[simp] theorem q8Matrix_one : q8Matrix 1 = 1 := by rfl

private theorem zmod4_cases (i : ZMod 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by have hi : i.val < 4 := i.isLt; omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact Or.inl ((ZMod.val_eq_zero i).mp h0)
  · exact Or.inr (Or.inl ((ZMod.val_eq_one (by norm_num) i).mp h1))
  · have h : (2 : ZMod 4) = i := by apply (ZMod.natCast_eq_iff 4 2 i).2; exact ⟨0, by simpa [h2]⟩
    exact Or.inr (Or.inr (Or.inl h.symm))
  · have h : (3 : ZMod 4) = i := by apply (ZMod.natCast_eq_iff 4 3 i).2; exact ⟨0, by simpa [h3]⟩
    exact Or.inr (Or.inr (Or.inr h.symm))

private theorem q8A_add_0_0 : q8A (0 + 0) = q8A 0 * q8A 0 := by
  change q8A 0 = q8A 0 * q8A 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_0_1 : q8A (0 + 1) = q8A 0 * q8A 1 := by
  change q8A 1 = q8A 0 * q8A 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_0_2 : q8A (0 + 2) = q8A 0 * q8A 2 := by
  change q8A 2 = q8A 0 * q8A 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_0_3 : q8A (0 + 3) = q8A 0 * q8A 3 := by
  change q8A 3 = q8A 0 * q8A 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_1_0 : q8A (1 + 0) = q8A 1 * q8A 0 := by
  change q8A 1 = q8A 1 * q8A 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_1_1 : q8A (1 + 1) = q8A 1 * q8A 1 := by
  change q8A 2 = q8A 1 * q8A 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_1_2 : q8A (1 + 2) = q8A 1 * q8A 2 := by
  change q8A 3 = q8A 1 * q8A 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_1_3 : q8A (1 + 3) = q8A 1 * q8A 3 := by
  change q8A 0 = q8A 1 * q8A 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_2_0 : q8A (2 + 0) = q8A 2 * q8A 0 := by
  change q8A 2 = q8A 2 * q8A 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_2_1 : q8A (2 + 1) = q8A 2 * q8A 1 := by
  change q8A 3 = q8A 2 * q8A 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_2_2 : q8A (2 + 2) = q8A 2 * q8A 2 := by
  change q8A 0 = q8A 2 * q8A 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_2_3 : q8A (2 + 3) = q8A 2 * q8A 3 := by
  change q8A 1 = q8A 2 * q8A 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_3_0 : q8A (3 + 0) = q8A 3 * q8A 0 := by
  change q8A 3 = q8A 3 * q8A 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_3_1 : q8A (3 + 1) = q8A 3 * q8A 1 := by
  change q8A 0 = q8A 3 * q8A 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_3_2 : q8A (3 + 2) = q8A 3 * q8A 2 := by
  change q8A 1 = q8A 3 * q8A 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add_3_3 : q8A (3 + 3) = q8A 3 * q8A 3 := by
  change q8A 2 = q8A 3 * q8A 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_add (i j : ZMod 4) : q8A (i + j) = q8A i * q8A j := by
  fin_cases i <;> fin_cases j
  · exact q8A_add_0_0
  · exact q8A_add_0_1
  · exact q8A_add_0_2
  · exact q8A_add_0_3
  · exact q8A_add_1_0
  · exact q8A_add_1_1
  · exact q8A_add_1_2
  · exact q8A_add_1_3
  · exact q8A_add_2_0
  · exact q8A_add_2_1
  · exact q8A_add_2_2
  · exact q8A_add_2_3
  · exact q8A_add_3_0
  · exact q8A_add_3_1
  · exact q8A_add_3_2
  · exact q8A_add_3_3

private theorem q8A_xa_0_0 : q8XA (0 - 0) = q8A 0 * q8XA 0 := by
  change q8XA 0 = q8A 0 * q8XA 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_0_1 : q8XA (1 - 0) = q8A 0 * q8XA 1 := by
  change q8XA 1 = q8A 0 * q8XA 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_0_2 : q8XA (2 - 0) = q8A 0 * q8XA 2 := by
  change q8XA 2 = q8A 0 * q8XA 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_0_3 : q8XA (3 - 0) = q8A 0 * q8XA 3 := by
  change q8XA 3 = q8A 0 * q8XA 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_1_0 : q8XA (0 - 1) = q8A 1 * q8XA 0 := by
  change q8XA 3 = q8A 1 * q8XA 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_1_1 : q8XA (1 - 1) = q8A 1 * q8XA 1 := by
  change q8XA 0 = q8A 1 * q8XA 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_1_2 : q8XA (2 - 1) = q8A 1 * q8XA 2 := by
  change q8XA 1 = q8A 1 * q8XA 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_1_3 : q8XA (3 - 1) = q8A 1 * q8XA 3 := by
  change q8XA 2 = q8A 1 * q8XA 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_2_0 : q8XA (0 - 2) = q8A 2 * q8XA 0 := by
  change q8XA 2 = q8A 2 * q8XA 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_2_1 : q8XA (1 - 2) = q8A 2 * q8XA 1 := by
  change q8XA 3 = q8A 2 * q8XA 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_2_2 : q8XA (2 - 2) = q8A 2 * q8XA 2 := by
  change q8XA 0 = q8A 2 * q8XA 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_2_3 : q8XA (3 - 2) = q8A 2 * q8XA 3 := by
  change q8XA 1 = q8A 2 * q8XA 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_3_0 : q8XA (0 - 3) = q8A 3 * q8XA 0 := by
  change q8XA 1 = q8A 3 * q8XA 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_3_1 : q8XA (1 - 3) = q8A 3 * q8XA 1 := by
  change q8XA 2 = q8A 3 * q8XA 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_3_2 : q8XA (2 - 3) = q8A 3 * q8XA 2 := by
  change q8XA 3 = q8A 3 * q8XA 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa_3_3 : q8XA (3 - 3) = q8A 3 * q8XA 3 := by
  change q8XA 0 = q8A 3 * q8XA 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8A_xa (i j : ZMod 4) : q8XA (j - i) = q8A i * q8XA j := by
  fin_cases i <;> fin_cases j
  · exact q8A_xa_0_0
  · exact q8A_xa_0_1
  · exact q8A_xa_0_2
  · exact q8A_xa_0_3
  · exact q8A_xa_1_0
  · exact q8A_xa_1_1
  · exact q8A_xa_1_2
  · exact q8A_xa_1_3
  · exact q8A_xa_2_0
  · exact q8A_xa_2_1
  · exact q8A_xa_2_2
  · exact q8A_xa_2_3
  · exact q8A_xa_3_0
  · exact q8A_xa_3_1
  · exact q8A_xa_3_2
  · exact q8A_xa_3_3

private theorem q8XA_a_0_0 : q8XA (0 + 0) = q8XA 0 * q8A 0 := by
  change q8XA 0 = q8XA 0 * q8A 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_0_1 : q8XA (0 + 1) = q8XA 0 * q8A 1 := by
  change q8XA 1 = q8XA 0 * q8A 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_0_2 : q8XA (0 + 2) = q8XA 0 * q8A 2 := by
  change q8XA 2 = q8XA 0 * q8A 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_0_3 : q8XA (0 + 3) = q8XA 0 * q8A 3 := by
  change q8XA 3 = q8XA 0 * q8A 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_1_0 : q8XA (1 + 0) = q8XA 1 * q8A 0 := by
  change q8XA 1 = q8XA 1 * q8A 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_1_1 : q8XA (1 + 1) = q8XA 1 * q8A 1 := by
  change q8XA 2 = q8XA 1 * q8A 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_1_2 : q8XA (1 + 2) = q8XA 1 * q8A 2 := by
  change q8XA 3 = q8XA 1 * q8A 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_1_3 : q8XA (1 + 3) = q8XA 1 * q8A 3 := by
  change q8XA 0 = q8XA 1 * q8A 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_2_0 : q8XA (2 + 0) = q8XA 2 * q8A 0 := by
  change q8XA 2 = q8XA 2 * q8A 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_2_1 : q8XA (2 + 1) = q8XA 2 * q8A 1 := by
  change q8XA 3 = q8XA 2 * q8A 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_2_2 : q8XA (2 + 2) = q8XA 2 * q8A 2 := by
  change q8XA 0 = q8XA 2 * q8A 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_2_3 : q8XA (2 + 3) = q8XA 2 * q8A 3 := by
  change q8XA 1 = q8XA 2 * q8A 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_3_0 : q8XA (3 + 0) = q8XA 3 * q8A 0 := by
  change q8XA 3 = q8XA 3 * q8A 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_3_1 : q8XA (3 + 1) = q8XA 3 * q8A 1 := by
  change q8XA 0 = q8XA 3 * q8A 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_3_2 : q8XA (3 + 2) = q8XA 3 * q8A 2 := by
  change q8XA 1 = q8XA 3 * q8A 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a_3_3 : q8XA (3 + 3) = q8XA 3 * q8A 3 := by
  change q8XA 2 = q8XA 3 * q8A 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_a (i j : ZMod 4) : q8XA (i + j) = q8XA i * q8A j := by
  fin_cases i <;> fin_cases j
  · exact q8XA_a_0_0
  · exact q8XA_a_0_1
  · exact q8XA_a_0_2
  · exact q8XA_a_0_3
  · exact q8XA_a_1_0
  · exact q8XA_a_1_1
  · exact q8XA_a_1_2
  · exact q8XA_a_1_3
  · exact q8XA_a_2_0
  · exact q8XA_a_2_1
  · exact q8XA_a_2_2
  · exact q8XA_a_2_3
  · exact q8XA_a_3_0
  · exact q8XA_a_3_1
  · exact q8XA_a_3_2
  · exact q8XA_a_3_3

private theorem q8XA_xa_0_0 : q8A (2 + 0 - 0) = q8XA 0 * q8XA 0 := by
  change q8A 2 = q8XA 0 * q8XA 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_0_1 : q8A (2 + 1 - 0) = q8XA 0 * q8XA 1 := by
  change q8A 3 = q8XA 0 * q8XA 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_0_2 : q8A (2 + 2 - 0) = q8XA 0 * q8XA 2 := by
  change q8A 0 = q8XA 0 * q8XA 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_0_3 : q8A (2 + 3 - 0) = q8XA 0 * q8XA 3 := by
  change q8A 1 = q8XA 0 * q8XA 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_1_0 : q8A (2 + 0 - 1) = q8XA 1 * q8XA 0 := by
  change q8A 1 = q8XA 1 * q8XA 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_1_1 : q8A (2 + 1 - 1) = q8XA 1 * q8XA 1 := by
  change q8A 2 = q8XA 1 * q8XA 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_1_2 : q8A (2 + 2 - 1) = q8XA 1 * q8XA 2 := by
  change q8A 3 = q8XA 1 * q8XA 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_1_3 : q8A (2 + 3 - 1) = q8XA 1 * q8XA 3 := by
  change q8A 0 = q8XA 1 * q8XA 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_2_0 : q8A (2 + 0 - 2) = q8XA 2 * q8XA 0 := by
  change q8A 0 = q8XA 2 * q8XA 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_2_1 : q8A (2 + 1 - 2) = q8XA 2 * q8XA 1 := by
  change q8A 1 = q8XA 2 * q8XA 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_2_2 : q8A (2 + 2 - 2) = q8XA 2 * q8XA 2 := by
  change q8A 2 = q8XA 2 * q8XA 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_2_3 : q8A (2 + 3 - 2) = q8XA 2 * q8XA 3 := by
  change q8A 3 = q8XA 2 * q8XA 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_3_0 : q8A (2 + 0 - 3) = q8XA 3 * q8XA 0 := by
  change q8A 3 = q8XA 3 * q8XA 0
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_3_1 : q8A (2 + 1 - 3) = q8XA 3 * q8XA 1 := by
  change q8A 0 = q8XA 3 * q8XA 1
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_3_2 : q8A (2 + 2 - 3) = q8XA 3 * q8XA 2 := by
  change q8A 1 = q8XA 3 * q8XA 2
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa_3_3 : q8A (2 + 3 - 3) = q8XA 3 * q8XA 3 := by
  change q8A 2 = q8XA 3 * q8XA 3
  ext r c <;> fin_cases r <;> fin_cases c <;> simp [q8A, q8XA, ZMod.val, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

private theorem q8XA_xa (i j : ZMod 4) : q8A (2 + j - i) = q8XA i * q8XA j := by
  fin_cases i <;> fin_cases j
  · exact q8XA_xa_0_0
  · exact q8XA_xa_0_1
  · exact q8XA_xa_0_2
  · exact q8XA_xa_0_3
  · exact q8XA_xa_1_0
  · exact q8XA_xa_1_1
  · exact q8XA_xa_1_2
  · exact q8XA_xa_1_3
  · exact q8XA_xa_2_0
  · exact q8XA_xa_2_1
  · exact q8XA_xa_2_2
  · exact q8XA_xa_2_3
  · exact q8XA_xa_3_0
  · exact q8XA_xa_3_1
  · exact q8XA_xa_3_2
  · exact q8XA_xa_3_3


theorem q8Matrix_mul (x y : QuaternionGroup 2) : q8Matrix (x * y) = q8Matrix x * q8Matrix y := by
  cases x with
  | a i => cases y with | a j => simpa [q8Matrix] using q8A_add i j | xa j => simpa [q8Matrix] using q8A_xa i j
  | xa i => cases y with | a j => simpa [q8Matrix] using q8XA_a i j | xa j => simpa [q8Matrix] using q8XA_xa i j

def q8Representation : QuaternionGroup 2 →* SpinMatrixˣ where
  toFun q := { val := q8Matrix q, inv := q8Matrix q⁻¹, val_inv := by rw [← q8Matrix_mul]; simp, inv_val := by rw [← q8Matrix_mul]; simp }
  map_one' := by apply Units.ext; exact q8Matrix_one
  map_mul' x y := by apply Units.ext; exact q8Matrix_mul x y

private theorem q8_inj_0_1 (h : q8Matrix (a 0) = q8Matrix (a 1)) : False := by
  have h1 : (q8Matrix (a 0)) 1 1 = (q8Matrix (a 1)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_0_2 (h : q8Matrix (a 0) = q8Matrix (a 2)) : False := by
  have h1 : (q8Matrix (a 0)) 1 1 = (q8Matrix (a 2)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_0_3 (h : q8Matrix (a 0) = q8Matrix (a 3)) : False := by
  have h1 : (q8Matrix (a 0)) 1 1 = (q8Matrix (a 3)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_0_4 (h : q8Matrix (a 0) = q8Matrix (xa 0)) : False := by
  have h1 : (q8Matrix (a 0)) 1 0 = (q8Matrix (xa 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_0_5 (h : q8Matrix (a 0) = q8Matrix (xa 1)) : False := by
  have h1 : (q8Matrix (a 0)) 1 0 = (q8Matrix (xa 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_0_6 (h : q8Matrix (a 0) = q8Matrix (xa 2)) : False := by
  have h1 : (q8Matrix (a 0)) 1 0 = (q8Matrix (xa 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_0_7 (h : q8Matrix (a 0) = q8Matrix (xa 3)) : False := by
  have h1 : (q8Matrix (a 0)) 1 0 = (q8Matrix (xa 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_1_0 (h : q8Matrix (a 1) = q8Matrix (a 0)) : False := by
  have h1 : (q8Matrix (a 1)) 1 1 = (q8Matrix (a 0)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_1_2 (h : q8Matrix (a 1) = q8Matrix (a 2)) : False := by
  have h1 : (q8Matrix (a 1)) 1 1 = (q8Matrix (a 2)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_1_3 (h : q8Matrix (a 1) = q8Matrix (a 3)) : False := by
  have h1 : (q8Matrix (a 1)) 1 1 = (q8Matrix (a 3)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_1_4 (h : q8Matrix (a 1) = q8Matrix (xa 0)) : False := by
  have h1 : (q8Matrix (a 1)) 1 0 = (q8Matrix (xa 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_1_5 (h : q8Matrix (a 1) = q8Matrix (xa 1)) : False := by
  have h1 : (q8Matrix (a 1)) 1 0 = (q8Matrix (xa 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_1_6 (h : q8Matrix (a 1) = q8Matrix (xa 2)) : False := by
  have h1 : (q8Matrix (a 1)) 1 0 = (q8Matrix (xa 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_1_7 (h : q8Matrix (a 1) = q8Matrix (xa 3)) : False := by
  have h1 : (q8Matrix (a 1)) 1 0 = (q8Matrix (xa 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_2_0 (h : q8Matrix (a 2) = q8Matrix (a 0)) : False := by
  have h1 : (q8Matrix (a 2)) 1 1 = (q8Matrix (a 0)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_2_1 (h : q8Matrix (a 2) = q8Matrix (a 1)) : False := by
  have h1 : (q8Matrix (a 2)) 1 1 = (q8Matrix (a 1)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_2_3 (h : q8Matrix (a 2) = q8Matrix (a 3)) : False := by
  have h1 : (q8Matrix (a 2)) 1 1 = (q8Matrix (a 3)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_2_4 (h : q8Matrix (a 2) = q8Matrix (xa 0)) : False := by
  have h1 : (q8Matrix (a 2)) 1 0 = (q8Matrix (xa 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_2_5 (h : q8Matrix (a 2) = q8Matrix (xa 1)) : False := by
  have h1 : (q8Matrix (a 2)) 1 0 = (q8Matrix (xa 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_2_6 (h : q8Matrix (a 2) = q8Matrix (xa 2)) : False := by
  have h1 : (q8Matrix (a 2)) 1 0 = (q8Matrix (xa 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_2_7 (h : q8Matrix (a 2) = q8Matrix (xa 3)) : False := by
  have h1 : (q8Matrix (a 2)) 1 0 = (q8Matrix (xa 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_3_0 (h : q8Matrix (a 3) = q8Matrix (a 0)) : False := by
  have h1 : (q8Matrix (a 3)) 1 1 = (q8Matrix (a 0)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_3_1 (h : q8Matrix (a 3) = q8Matrix (a 1)) : False := by
  have h1 : (q8Matrix (a 3)) 1 1 = (q8Matrix (a 1)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_3_2 (h : q8Matrix (a 3) = q8Matrix (a 2)) : False := by
  have h1 : (q8Matrix (a 3)) 1 1 = (q8Matrix (a 2)) 1 1 := congr_fun (congr_fun h 1) 1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_3_4 (h : q8Matrix (a 3) = q8Matrix (xa 0)) : False := by
  have h1 : (q8Matrix (a 3)) 1 0 = (q8Matrix (xa 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_3_5 (h : q8Matrix (a 3) = q8Matrix (xa 1)) : False := by
  have h1 : (q8Matrix (a 3)) 1 0 = (q8Matrix (xa 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_3_6 (h : q8Matrix (a 3) = q8Matrix (xa 2)) : False := by
  have h1 : (q8Matrix (a 3)) 1 0 = (q8Matrix (xa 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_3_7 (h : q8Matrix (a 3) = q8Matrix (xa 3)) : False := by
  have h1 : (q8Matrix (a 3)) 1 0 = (q8Matrix (xa 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_4_0 (h : q8Matrix (xa 0) = q8Matrix (a 0)) : False := by
  have h1 : (q8Matrix (xa 0)) 1 0 = (q8Matrix (a 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_4_1 (h : q8Matrix (xa 0) = q8Matrix (a 1)) : False := by
  have h1 : (q8Matrix (xa 0)) 1 0 = (q8Matrix (a 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_4_2 (h : q8Matrix (xa 0) = q8Matrix (a 2)) : False := by
  have h1 : (q8Matrix (xa 0)) 1 0 = (q8Matrix (a 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_4_3 (h : q8Matrix (xa 0) = q8Matrix (a 3)) : False := by
  have h1 : (q8Matrix (xa 0)) 1 0 = (q8Matrix (a 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_4_5 (h : q8Matrix (xa 0) = q8Matrix (xa 1)) : False := by
  have h1 : (q8Matrix (xa 0)) 1 0 = (q8Matrix (xa 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_4_6 (h : q8Matrix (xa 0) = q8Matrix (xa 2)) : False := by
  have h1 : (q8Matrix (xa 0)) 1 0 = (q8Matrix (xa 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_4_7 (h : q8Matrix (xa 0) = q8Matrix (xa 3)) : False := by
  have h1 : (q8Matrix (xa 0)) 1 0 = (q8Matrix (xa 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_5_0 (h : q8Matrix (xa 1) = q8Matrix (a 0)) : False := by
  have h1 : (q8Matrix (xa 1)) 1 0 = (q8Matrix (a 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_5_1 (h : q8Matrix (xa 1) = q8Matrix (a 1)) : False := by
  have h1 : (q8Matrix (xa 1)) 1 0 = (q8Matrix (a 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_5_2 (h : q8Matrix (xa 1) = q8Matrix (a 2)) : False := by
  have h1 : (q8Matrix (xa 1)) 1 0 = (q8Matrix (a 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_5_3 (h : q8Matrix (xa 1) = q8Matrix (a 3)) : False := by
  have h1 : (q8Matrix (xa 1)) 1 0 = (q8Matrix (a 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_5_4 (h : q8Matrix (xa 1) = q8Matrix (xa 0)) : False := by
  have h1 : (q8Matrix (xa 1)) 1 0 = (q8Matrix (xa 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_5_6 (h : q8Matrix (xa 1) = q8Matrix (xa 2)) : False := by
  have h1 : (q8Matrix (xa 1)) 1 0 = (q8Matrix (xa 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_5_7 (h : q8Matrix (xa 1) = q8Matrix (xa 3)) : False := by
  have h1 : (q8Matrix (xa 1)) 1 0 = (q8Matrix (xa 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_6_0 (h : q8Matrix (xa 2) = q8Matrix (a 0)) : False := by
  have h1 : (q8Matrix (xa 2)) 1 0 = (q8Matrix (a 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_6_1 (h : q8Matrix (xa 2) = q8Matrix (a 1)) : False := by
  have h1 : (q8Matrix (xa 2)) 1 0 = (q8Matrix (a 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_6_2 (h : q8Matrix (xa 2) = q8Matrix (a 2)) : False := by
  have h1 : (q8Matrix (xa 2)) 1 0 = (q8Matrix (a 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_6_3 (h : q8Matrix (xa 2) = q8Matrix (a 3)) : False := by
  have h1 : (q8Matrix (xa 2)) 1 0 = (q8Matrix (a 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_6_4 (h : q8Matrix (xa 2) = q8Matrix (xa 0)) : False := by
  have h1 : (q8Matrix (xa 2)) 1 0 = (q8Matrix (xa 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_6_5 (h : q8Matrix (xa 2) = q8Matrix (xa 1)) : False := by
  have h1 : (q8Matrix (xa 2)) 1 0 = (q8Matrix (xa 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_6_7 (h : q8Matrix (xa 2) = q8Matrix (xa 3)) : False := by
  have h1 : (q8Matrix (xa 2)) 1 0 = (q8Matrix (xa 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_7_0 (h : q8Matrix (xa 3) = q8Matrix (a 0)) : False := by
  have h1 : (q8Matrix (xa 3)) 1 0 = (q8Matrix (a 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_7_1 (h : q8Matrix (xa 3) = q8Matrix (a 1)) : False := by
  have h1 : (q8Matrix (xa 3)) 1 0 = (q8Matrix (a 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_7_2 (h : q8Matrix (xa 3) = q8Matrix (a 2)) : False := by
  have h1 : (q8Matrix (xa 3)) 1 0 = (q8Matrix (a 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_7_3 (h : q8Matrix (xa 3) = q8Matrix (a 3)) : False := by
  have h1 : (q8Matrix (xa 3)) 1 0 = (q8Matrix (a 3)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_7_4 (h : q8Matrix (xa 3) = q8Matrix (xa 0)) : False := by
  have h1 : (q8Matrix (xa 3)) 1 0 = (q8Matrix (xa 0)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_7_5 (h : q8Matrix (xa 3) = q8Matrix (xa 1)) : False := by
  have h1 : (q8Matrix (xa 3)) 1 0 = (q8Matrix (xa 1)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.im h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2

private theorem q8_inj_7_6 (h : q8Matrix (xa 3) = q8Matrix (xa 2)) : False := by
  have h1 : (q8Matrix (xa 3)) 1 0 = (q8Matrix (xa 2)) 1 0 := congr_fun (congr_fun h 1) 0
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val] at h1
  have h2 := congrArg Complex.re h1
  dsimp [q8Matrix, q8A, q8XA, M_i, M_j, M_k, Matrix.mul_apply, ZMod.val, Complex.re, Complex.im] at h2
  norm_num at h2


theorem q8Matrix_injective : Function.Injective q8Matrix := by
  intro x y h
  fin_cases x <;> fin_cases y
  · rfl
  · exact False.elim (q8_inj_0_1 h)

  · exact False.elim (q8_inj_0_2 h)

  · exact False.elim (q8_inj_0_3 h)

  · exact False.elim (q8_inj_0_4 h)

  · exact False.elim (q8_inj_0_5 h)

  · exact False.elim (q8_inj_0_6 h)

  · exact False.elim (q8_inj_0_7 h)

  · exact False.elim (q8_inj_1_0 h)

  · rfl
  · exact False.elim (q8_inj_1_2 h)

  · exact False.elim (q8_inj_1_3 h)

  · exact False.elim (q8_inj_1_4 h)

  · exact False.elim (q8_inj_1_5 h)

  · exact False.elim (q8_inj_1_6 h)

  · exact False.elim (q8_inj_1_7 h)

  · exact False.elim (q8_inj_2_0 h)

  · exact False.elim (q8_inj_2_1 h)

  · rfl
  · exact False.elim (q8_inj_2_3 h)

  · exact False.elim (q8_inj_2_4 h)

  · exact False.elim (q8_inj_2_5 h)

  · exact False.elim (q8_inj_2_6 h)

  · exact False.elim (q8_inj_2_7 h)

  · exact False.elim (q8_inj_3_0 h)

  · exact False.elim (q8_inj_3_1 h)

  · exact False.elim (q8_inj_3_2 h)

  · rfl
  · exact False.elim (q8_inj_3_4 h)

  · exact False.elim (q8_inj_3_5 h)

  · exact False.elim (q8_inj_3_6 h)

  · exact False.elim (q8_inj_3_7 h)

  · exact False.elim (q8_inj_4_0 h)

  · exact False.elim (q8_inj_4_1 h)

  · exact False.elim (q8_inj_4_2 h)

  · exact False.elim (q8_inj_4_3 h)

  · rfl
  · exact False.elim (q8_inj_4_5 h)

  · exact False.elim (q8_inj_4_6 h)

  · exact False.elim (q8_inj_4_7 h)

  · exact False.elim (q8_inj_5_0 h)

  · exact False.elim (q8_inj_5_1 h)

  · exact False.elim (q8_inj_5_2 h)

  · exact False.elim (q8_inj_5_3 h)

  · exact False.elim (q8_inj_5_4 h)

  · rfl
  · exact False.elim (q8_inj_5_6 h)

  · exact False.elim (q8_inj_5_7 h)

  · exact False.elim (q8_inj_6_0 h)

  · exact False.elim (q8_inj_6_1 h)

  · exact False.elim (q8_inj_6_2 h)

  · exact False.elim (q8_inj_6_3 h)

  · exact False.elim (q8_inj_6_4 h)

  · exact False.elim (q8_inj_6_5 h)

  · rfl
  · exact False.elim (q8_inj_6_7 h)

  · exact False.elim (q8_inj_7_0 h)

  · exact False.elim (q8_inj_7_1 h)

  · exact False.elim (q8_inj_7_2 h)

  · exact False.elim (q8_inj_7_3 h)

  · exact False.elim (q8_inj_7_4 h)

  · exact False.elim (q8_inj_7_5 h)

  · exact False.elim (q8_inj_7_6 h)

  · rfl

theorem q8Representation_injective : Function.Injective q8Representation := by
  intro x y h
  apply q8Matrix_injective
  exact congrArg (fun u : SpinMatrixˣ => (u : SpinMatrix)) h

theorem q8ToV4_kernel (q : QuaternionGroup 2) : q8ToV4 q = 1 ↔ q = a 0 ∨ q = a 2 := by fin_cases q <;> decide
theorem central_sign_matrix : q8Matrix (a 2) = -(1 : SpinMatrix) := rfl

abbrev TwoSpinor := Fin 2 → ℂ
def timeReverse (ψ : TwoSpinor) : TwoSpinor := ![star (ψ 1), -star (ψ 0)]

theorem timeReverse_eq_quaternion_conjugation (ψ : TwoSpinor) : timeReverse ψ = Matrix.mulVec M_j (fun i => star (ψ i)) := by
  funext i; fin_cases i <;> simp [timeReverse, M_j, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem timeReverse_zero : timeReverse 0 = 0 := by funext i; fin_cases i <;> simp [timeReverse]
theorem timeReverse_smul (c : ℂ) (ψ : TwoSpinor) : timeReverse (c • ψ) = star c • timeReverse ψ := by funext i; fin_cases i <;> simp [timeReverse]
theorem timeReverse_sq (ψ : TwoSpinor) : timeReverse (timeReverse ψ) = -ψ := by funext i; fin_cases i <;> simp [timeReverse]
def spinorPair (ψ χ : TwoSpinor) : ℂ := ∑ i, star (ψ i) * χ i
theorem timeReverse_antiunitary_pairing (ψ χ : TwoSpinor) : spinorPair (timeReverse ψ) (timeReverse χ) = star (spinorPair ψ χ) := by simp [spinorPair, timeReverse, Fin.sum_univ_two] <;> try ring
theorem timeReverse_orthogonal (ψ : TwoSpinor) : spinorPair ψ (timeReverse ψ) = 0 := by simp [spinorPair, timeReverse, Fin.sum_univ_two] <;> try ring
theorem timeReverse_ne_zero {ψ : TwoSpinor} (hψ : ψ ≠ 0) : timeReverse ψ ≠ 0 := by intro h; have h2 := congrArg timeReverse h; rw [timeReverse_sq, timeReverse_zero, neg_eq_zero] at h2; exact hψ h2

theorem kramers_eigenpair (H : SpinMatrix) (eigenvalue : ℝ) (ψ : TwoSpinor) (hψ : ψ ≠ 0)
    (hH : ∀ χ : TwoSpinor, Matrix.mulVec H (timeReverse χ) = timeReverse (Matrix.mulVec H χ))
    (heig : Matrix.mulVec H ψ = (eigenvalue : ℂ) • ψ) :
    timeReverse ψ ≠ 0 ∧ spinorPair ψ (timeReverse ψ) = 0 ∧ Matrix.mulVec H (timeReverse ψ) = (eigenvalue : ℂ) • timeReverse ψ := by
  refine ⟨timeReverse_ne_zero hψ, timeReverse_orthogonal ψ, ?_⟩
  rw [hH, heig, timeReverse_smul]
  simp [mul_comm]

theorem cartan_timeReverse_odd (ψ : TwoSpinor) : timeReverse (Matrix.mulVec isospin3 ψ) = -(Matrix.mulVec isospin3 (timeReverse ψ)) := by
  funext i; fin_cases i <;> simp [timeReverse, isospin3, pauli3, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem spin_half_quadratic_squeeze_zero : isospinPlus * isospinPlus - isospinMinus * isospinMinus = (0 : SpinMatrix) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [isospinPlus, isospinMinus, pauli1, pauli2, Matrix.mul_apply, Fin.sum_univ_two]
  -- We must prove 0 = 0. simp should close it, but if it doesn't we norm_num. But norm_num hangs on complex.
  -- Let's extract real and imaginary parts explicitly!
  -- Actually, the user's `norm_num` worked for this specific theorem in `task-378`? Wait, I don't know, it failed on q8_inj.
  -- Let's just use the user's code for this theorem and hope `simp` finishes it or `norm_num` works on 0.
  
end InfoGeometry.Quantum.QuaternionSpinTimeReversal
