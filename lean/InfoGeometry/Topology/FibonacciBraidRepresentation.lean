import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Topology.FibonacciFR
import InfoGeometry.Categorical.FibonacciBraiding

open Matrix

namespace InfoGeometry.Topology.FibonacciBraidRepresentation

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

/-! ## Explicit interface to the finite categorical owner -/

/--
The topological generator predicate is inherited from the already proved finite
categorical Artin identity once the two presentations are explicitly identified.
The hypotheses are intentionally exposed: this theorem does not infer a choice
of root of unity or identify an arbitrary `FibonacciData` with a categorical
parameter package.
-/
theorem is_fibonacci_B3_artin_relation_of_finite_categorical
    (D : FibonacciData) (q : Units ℂ) (τ s : ℂ)
    (hR : R_matrix D =
      InfoGeometry.Canonical.FiniteFibonacciFusionMatrix.fibonacciRMatrix q)
    (hF : F_matrix D =
      InfoGeometry.Canonical.FiniteFibonacciFusionMatrix.fibonacciFusionMatrix τ s)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    is_fibonacci_B3_artin_relation D := by
  unfold is_fibonacci_B3_artin_relation B1 B2
  rw [hR, hF]
  exact InfoGeometry.Categorical.FibonacciBraiding.artin_relation
    q τ s hq_inv hq_pow3 hq5 h_poly hτ hs

end InfoGeometry.Topology.FibonacciBraidRepresentation
