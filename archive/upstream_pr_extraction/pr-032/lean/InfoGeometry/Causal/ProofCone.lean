import Mathlib.Tactic

open Matrix

namespace InfoGeometry.Causal.ProofCone

/-!
BUCKET 1: CLOSED FINITE THEOREMS:
  - future_idempotent
  - past_idempotent
  - future_past_zero
  - past_future_zero
  - hodge_laplacian_zero
  - dirac_operator_identity
  - dirac_laplacian_identity
  - chirality_recovers_orientation
  - orientation_involutive
  - det_orientation
  - trace_orientation

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES:
  - None in this finite 2x2 proof-cone model.

BUCKET 3: OPEN CLOSURE DEBT:
  - This file proves the finite algebraic proof-cone skeleton only.
  - It does not assert extraction from `.olean`, InfoTree correctness, ArangoDB ingestion,
    graph spectral completeness, or LeanTrail proposal soundness.
-/

abbrev CausalMat2 := Matrix (Fin 2) (Fin 2) ℝ

def mul (A B : CausalMat2) : CausalMat2 :=
  A * B

def add (A B : CausalMat2) : CausalMat2 :=
  A + B

def sub (A B : CausalMat2) : CausalMat2 :=
  A - B

def zero : CausalMat2 :=
  0

def one : CausalMat2 :=
  1

def orientation : CausalMat2 :=
  !![0, 1; 1, 0]

noncomputable def future : CausalMat2 :=
  !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

noncomputable def past : CausalMat2 :=
  !![1 / 2, -1 / 2; -1 / 2, 1 / 2]

noncomputable def hodgeLaplacian : CausalMat2 :=
  add (mul future past) (mul past future)

noncomputable def diracOperator : CausalMat2 :=
  add future past

noncomputable def diracLaplacian : CausalMat2 :=
  mul diracOperator diracOperator

noncomputable def chirality : CausalMat2 :=
  sub future past

def det (A : CausalMat2) : ℝ :=
  Matrix.det A

def trace (A : CausalMat2) : ℝ :=
  Matrix.trace A

@[simp] theorem future_idempotent :
    mul future future = future := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [mul, future, Matrix.mul_apply]

@[simp] theorem past_idempotent :
    mul past past = past := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [mul, past, Matrix.mul_apply]

@[simp] theorem future_past_zero :
    mul future past = zero := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [mul, future, past, zero, Matrix.mul_apply]

@[simp] theorem past_future_zero :
    mul past future = zero := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [mul, future, past, zero, Matrix.mul_apply]

@[simp] theorem hodge_laplacian_zero :
    hodgeLaplacian = zero := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [hodgeLaplacian, add, mul, future, past, zero, Matrix.mul_apply]

@[simp] theorem dirac_operator_identity :
    diracOperator = one := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracOperator, add, future, past, one]

@[simp] theorem dirac_laplacian_identity :
    diracLaplacian = one := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [diracLaplacian, diracOperator, add, mul, future, past, one, Matrix.mul_apply]

@[simp] theorem chirality_recovers_orientation :
    chirality = orientation := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [chirality, sub, future, past, orientation]

@[simp] theorem orientation_involutive :
    mul orientation orientation = one := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [mul, orientation, one, Matrix.mul_apply]

@[simp] theorem det_orientation :
    det orientation = -1 := by
  norm_num [det, orientation, Matrix.det_fin_two]

@[simp] theorem trace_orientation :
    trace orientation = 0 := by
  norm_num [trace, orientation, Matrix.trace]

end InfoGeometry.Causal.ProofCone
