import Mathlib

open Set Matrix

namespace InfoGeometry.Causal.ProofTopology

/-!
# Proof Topology

This file packages the finite proof-DAG layer, the local 2×2 chiral/Hodge
algebra, and the sensing bridge as an interpretation theorem.

It deliberately does not identify graph acyclicity with `Δ_H = 0` by
definition. The latter is a local projector law; the former is an
order-theoretic property of the proof dependency relation.
-/

/-! ## Bucket 1: Causal Cones and Order Theory -/

section CausalCones

variable {α : Type*} [Preorder α]

/-- Forward cone: all consequences reachable from `a`. -/
def forwardCone (a : α) : Set α :=
  {b | a ≤ b}

/-- Backward cone: all premises required by `a`. -/
def backwardCone (a : α) : Set α :=
  {b | b ≤ a}

@[simp] theorem forwardCone_self (a : α) :
    a ∈ forwardCone a := by
  exact le_rfl

@[simp] theorem backwardCone_self (a : α) :
    a ∈ backwardCone a := by
  exact le_rfl

theorem forwardCone_trans {a b c : α}
    (hab : b ∈ forwardCone a)
    (hbc : c ∈ forwardCone b) :
    c ∈ forwardCone a := by
  exact le_trans hab hbc

theorem backwardCone_trans {a b c : α}
    (hab : b ∈ backwardCone a)
    (hcb : c ∈ backwardCone b) :
    c ∈ backwardCone a := by
  exact le_trans hcb hab

end CausalCones

section CausalConesAntisymm

variable {α : Type*} [PartialOrder α]

theorem cones_intersect_self_of_antisymm (a : α) :
    forwardCone a ∩ backwardCone a = {a} := by
  ext b
  constructor
  · intro hb
    have hba : b ≤ a := hb.2
    have hab : a ≤ b := hb.1
    exact Set.mem_singleton_iff.mpr (le_antisymm hba hab)
  · intro hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact ⟨le_rfl, le_rfl⟩

theorem no_two_way_loop_of_partial_order {a b : α}
    (hab : b ∈ forwardCone a)
    (hba : b ∈ backwardCone a) :
    b = a := by
  exact le_antisymm hba hab

end CausalConesAntisymm

/-! ## Bucket 1: Local 2×2 Chiral / Hodge Algebra -/

abbrev CausalMat2 := Matrix (Fin 2) (Fin 2) ℝ

def cmul (A B : CausalMat2) : CausalMat2 :=
  A * B

def cadd (A B : CausalMat2) : CausalMat2 :=
  A + B

def csub (A B : CausalMat2) : CausalMat2 :=
  A - B

def czero : CausalMat2 :=
  0

def coneId : CausalMat2 :=
  1

/-- Orientation reversal / local time-reversal block. -/
def orientation : CausalMat2 :=
  !![0, 1; 1, 0]

/-- Local future projector `d = (I + O)/2`. -/
noncomputable def future : CausalMat2 :=
  !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

/-- Local past projector `δ = (I - O)/2`. -/
noncomputable def past : CausalMat2 :=
  !![1 / 2, -1 / 2; -1 / 2, 1 / 2]

noncomputable def localHodgeLaplacian : CausalMat2 :=
  cadd (cmul future past) (cmul past future)

noncomputable def diracOperator : CausalMat2 :=
  cadd future past

noncomputable def diracLaplacian : CausalMat2 :=
  cmul diracOperator diracOperator

noncomputable def chirality : CausalMat2 :=
  csub future past

def det (A : CausalMat2) : ℝ :=
  Matrix.det A

def trace (A : CausalMat2) : ℝ :=
  Matrix.trace A

@[simp] theorem future_idempotent :
    cmul future future = future := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [cmul, future, Matrix.mul_apply]

@[simp] theorem past_idempotent :
    cmul past past = past := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [cmul, past, Matrix.mul_apply]

@[simp] theorem future_past_zero :
    cmul future past = czero := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [cmul, future, past, czero, Matrix.mul_apply]

@[simp] theorem past_future_zero :
    cmul past future = czero := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [cmul, future, past, czero, Matrix.mul_apply]

@[simp] theorem local_hodge_laplacian_zero :
    localHodgeLaplacian = czero := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [localHodgeLaplacian, cadd, cmul, future, past, czero, Matrix.mul_apply]

@[simp] theorem dirac_operator_identity :
    diracOperator = coneId := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracOperator, cadd, future, past, coneId]

@[simp] theorem dirac_laplacian_identity :
    diracLaplacian = coneId := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracLaplacian, diracOperator, cadd, cmul, future, past, coneId, Matrix.mul_apply]

@[simp] theorem chirality_recovers_orientation :
    chirality = orientation := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [chirality, csub, future, past, orientation]

@[simp] theorem orientation_involutive :
    cmul orientation orientation = coneId := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [cmul, orientation, coneId, Matrix.mul_apply]

@[simp] theorem det_orientation :
    det orientation = -1 := by
  norm_num [det, orientation, Matrix.det_fin_two]

@[simp] theorem trace_orientation :
    trace orientation = 0 := by
  norm_num [trace, orientation, Matrix.trace]

end InfoGeometry.Causal.ProofTopology
