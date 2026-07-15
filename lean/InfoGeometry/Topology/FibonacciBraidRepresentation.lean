import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Topology.FibonacciFR

open Matrix

namespace FibonacciBraidRepresentation

open FibonacciFR

/-- Braiding Generator B1 = R -/
noncomputable def B1 (D : FibonacciData) : Matrix (Fin 2) (Fin 2) ℂ := R_matrix D

/-- Braiding Generator B2 = F R F -/
noncomputable def B2 (D : FibonacciData) : Matrix (Fin 2) (Fin 2) ℂ := F_matrix D * R_matrix D * F_matrix D

/-- The genuine Fibonacci sector Artin braid relation property -/
def is_fibonacci_B3_artin_relation (D : FibonacciData) : Prop :=
  B1 D * B2 D * B1 D = B2 D * B1 D * B2 D

/-- The Fibonacci braiding does NOT collapse to the symmetric group S3 closure. -/
def is_fibonacci_not_s3_closure (D : FibonacciData) : Prop :=
  B1 D * B1 D ≠ 1 ∧ B2 D * B2 D ≠ 1

end FibonacciBraidRepresentation
