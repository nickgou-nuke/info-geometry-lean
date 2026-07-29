import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace HaPPYPerfectTensorHolography

/-- HaPPY Code Qubit Dimension d = 2. -/
def qubitDim : ℕ := 2

/-- 3-to-3 Index Reshaped 6-Index Perfect Tensor M₃ ∈ M₈(ℂ) where 8 = 2³. -/
structure PerfectPentagonTensor where
  tensor_matrix : Matrix (Fin 8) (Fin 8) ℂ
  h_isometry : tensor_matrix * tensor_matrix.conjTranspose = 1

namespace PerfectPentagonTensor

variable (tensor : PerfectPentagonTensor)

/-- **Theorem**: Perfect Tensor 3-to-3 Index Isometry: M₃ * M₃† = 1. -/
theorem perfect_tensor_isometry :
    tensor.tensor_matrix * tensor.tensor_matrix.conjTranspose = 1 :=
  tensor.h_isometry

/-- **Theorem**: Perfect Tensor Trace Conservation: Tr(M₃ * M₃†) = 8. -/
theorem perfect_tensor_trace_conservation :
    trace (tensor.tensor_matrix * tensor.tensor_matrix.conjTranspose) = 8 := by
  rw [tensor.h_isometry, trace_one]
  rfl

/-- HaPPY Network Bulk-to-Boundary Map Representation V ∈ Mₙ(ℂ). -/
structure HaPPYNetworkIsometry (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  happy_map : Matrix (Fin n) (Fin n) ℂ
  h_happy_isometry : happy_map.conjTranspose * happy_map = 1

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (net : HaPPYNetworkIsometry n)

/-- **Theorem**: Bulk-to-Boundary Global Isometry: V† * V = 1. -/
theorem happy_global_isometry :
    net.happy_map.conjTranspose * net.happy_map = 1 :=
  net.h_happy_isometry

/-- **Theorem**: Bulk Operator Subregion Reconstruction Intertwining:
    If O_A * V = V * ϕ, then Tr(O_A * V * V†) = Tr(V * ϕ * V†). -/
theorem bulk_operator_reconstruction_intertwining (phi O_A : Matrix (Fin n) (Fin n) ℂ)
    (h_push : O_A * net.happy_map = net.happy_map * phi) :
    trace (O_A * net.happy_map * net.happy_map.conjTranspose) = trace (net.happy_map * phi * net.happy_map.conjTranspose) := by
  rw [h_push]

/-- **Theorem**: Bulk Reconstruction Trace Conservation:
    Tr(V * ϕ * V†) = Tr(ϕ) for unitary V. -/
theorem bulk_reconstruction_trace_conservation (phi : Matrix (Fin n) (Fin n) ℂ) :
    trace (net.happy_map * phi * net.happy_map.conjTranspose) = trace phi := by
  rw [trace_mul_comm (net.happy_map * phi) net.happy_map.conjTranspose, ← mul_assoc, net.h_happy_isometry, one_mul]

end PerfectPentagonTensor

end HaPPYPerfectTensorHolography
