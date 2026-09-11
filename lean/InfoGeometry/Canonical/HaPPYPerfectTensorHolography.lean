import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
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
  tensor_matrix : Matrix.unitaryGroup (Fin 8) ℂ

namespace PerfectPentagonTensor

variable (tensor : PerfectPentagonTensor)

def tensorVal : Matrix (Fin 8) (Fin 8) ℂ := tensor.tensor_matrix

theorem h_isometry : tensorVal tensor * (tensorVal tensor).conjTranspose = 1 := by
  change (tensor.tensor_matrix : Matrix (Fin 8) (Fin 8) ℂ) *
      (tensor.tensor_matrix : Matrix (Fin 8) (Fin 8) ℂ).conjTranspose = 1
  exact Matrix.mem_unitaryGroup_iff.mp tensor.tensor_matrix.2

/-- **Theorem**: Perfect Tensor 3-to-3 Index Isometry: M₃ * M₃† = 1. -/
theorem perfect_tensor_isometry :
    tensorVal tensor * (tensorVal tensor).conjTranspose = 1 :=
  h_isometry tensor

/-- **Theorem**: Perfect Tensor Trace Conservation: Tr(M₃ * M₃†) = 8. -/
theorem perfect_tensor_trace_conservation :
    trace (tensorVal tensor * (tensorVal tensor).conjTranspose) = 8 := by
  rw [h_isometry tensor, trace_one]
  rfl

/-- HaPPY Network Bulk-to-Boundary Map Representation V ∈ Mₙ(ℂ). -/
structure HaPPYNetworkIsometry (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  happy_map : Matrix.unitaryGroup (Fin n) ℂ

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] (net : HaPPYNetworkIsometry n)

def happyMapVal : Matrix (Fin n) (Fin n) ℂ := net.happy_map

theorem h_happy_isometry :
    (happyMapVal net).conjTranspose * happyMapVal net = 1 := by
  change (net.happy_map : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
      (net.happy_map : Matrix (Fin n) (Fin n) ℂ) = 1
  exact Matrix.mem_unitaryGroup_iff'.mp net.happy_map.2

/-- **Theorem**: Bulk-to-Boundary Global Isometry: V† * V = 1. -/
theorem happy_global_isometry :
    (happyMapVal net).conjTranspose * happyMapVal net = 1 :=
  h_happy_isometry net

/-- **Theorem**: Bulk Operator Subregion Reconstruction Intertwining:
    If O_A * V = V * ϕ, then Tr(O_A * V * V†) = Tr(V * ϕ * V†). -/
theorem bulk_operator_reconstruction_intertwining (phi O_A : Matrix (Fin n) (Fin n) ℂ)
    (h_push : O_A * happyMapVal net = happyMapVal net * phi) :
    trace (O_A * happyMapVal net * (happyMapVal net).conjTranspose) =
      trace (happyMapVal net * phi * (happyMapVal net).conjTranspose) := by
  rw [h_push]

/-- **Theorem**: Bulk Reconstruction Trace Conservation:
    Tr(V * ϕ * V†) = Tr(ϕ) for unitary V. -/
theorem bulk_reconstruction_trace_conservation (phi : Matrix (Fin n) (Fin n) ℂ) :
    trace (happyMapVal net * phi * (happyMapVal net).conjTranspose) = trace phi := by
  rw [trace_mul_comm (happyMapVal net * phi) (happyMapVal net).conjTranspose,
    ← mul_assoc, h_happy_isometry net, one_mul]

end PerfectPentagonTensor

end HaPPYPerfectTensorHolography
