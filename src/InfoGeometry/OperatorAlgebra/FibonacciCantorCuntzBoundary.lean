import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Fibonacci Cantor--Cuntz--Krieger boundary

Finite owner for the intrinsic Fibonacci admissible-path boundary.  The
adjacency matrix is the golden-mean matrix

```text
A = [[0, 1],
     [1, 1]]
```

This is a Cuntz--Krieger adjacency surface, not a representation theorem for a
completed operator algebra.

#### BUCKET 1: CLOSED FINITE THEOREMS

`fibonacciAdjacency_entries` and `fibonacciPathCount_recursion`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

No Hilbert-space representation of `O_A`, no K-theory computation, and no
physical null-boundary anyon model is proved here.
-/

namespace InfoGeometry.OperatorAlgebra.FibonacciCantorCuntzBoundary

open Matrix

/-- Two Fibonacci fusion path labels: vacuum `1` and nontrivial charge `τ`. -/
inductive FibCharge
  | one
  | tau
deriving DecidableEq, Repr

/-- Encode the two labels as `Fin 2`, with `0 = 1` and `1 = τ`. -/
def chargeIndex : FibCharge → Fin 2
  | FibCharge.one => 0
  | FibCharge.tau => 1

/-- The intrinsic Fibonacci/golden-mean adjacency matrix. -/
def fibonacciAdjacency : Matrix (Fin 2) (Fin 2) ℕ :=
  !![0, 1;
     1, 1]

/-- Infinite admissible path space for the Fibonacci adjacency matrix. -/
def AdmissiblePathSpace :=
  { x : ℕ → Fin 2 // ∀ i, fibonacciAdjacency (x i) (x (i + 1)) = 1 }

/-- Fibonacci path-count recursion used by the finite boundary readout. -/
def fibonacciPathCount : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => fibonacciPathCount (n + 1) + fibonacciPathCount n

/-- The golden-mean adjacency entries are exactly `[[0,1],[1,1]]`. -/
theorem fibonacciAdjacency_entries :
    fibonacciAdjacency 0 0 = 0 ∧
      fibonacciAdjacency 0 1 = 1 ∧
      fibonacciAdjacency 1 0 = 1 ∧
      fibonacciAdjacency 1 1 = 1 := by
  simp [fibonacciAdjacency]

/-- The path-count function satisfies the Fibonacci recursion by definition. -/
theorem fibonacciPathCount_recursion (n : ℕ) :
    fibonacciPathCount (n + 2) =
      fibonacciPathCount (n + 1) + fibonacciPathCount n := by
  rfl

/-- The first two boundary path counts are both one. -/
theorem fibonacciPathCount_initial :
    fibonacciPathCount 0 = 1 ∧ fibonacciPathCount 1 = 1 := by
  simp [fibonacciPathCount]

/-- Consolidated finite Fibonacci boundary packet. -/
theorem fibonacci_boundary_packet :
    fibonacciAdjacency 0 0 = 0 ∧
      fibonacciAdjacency 0 1 = 1 ∧
      fibonacciAdjacency 1 0 = 1 ∧
      fibonacciAdjacency 1 1 = 1 ∧
      fibonacciPathCount 0 = 1 ∧
      fibonacciPathCount 1 = 1 ∧
      ∀ n : ℕ,
        fibonacciPathCount (n + 2) =
          fibonacciPathCount (n + 1) + fibonacciPathCount n := by
  exact ⟨
    fibonacciAdjacency_entries.1,
    fibonacciAdjacency_entries.2.1,
    fibonacciAdjacency_entries.2.2.1,
    fibonacciAdjacency_entries.2.2.2,
    fibonacciPathCount_initial.1,
    fibonacciPathCount_initial.2,
    fibonacciPathCount_recursion⟩

end InfoGeometry.OperatorAlgebra.FibonacciCantorCuntzBoundary
