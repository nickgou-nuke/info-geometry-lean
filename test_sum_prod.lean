import Mathlib
import InfoGeometry.Arithmetic.SplitMajoranaPrimon
open scoped BigOperators

inductive Occupancy where | empty | occupied deriving DecidableEq, Fintype, Repr
def localParityEigenvalue : Occupancy → ℝ | Occupancy.empty => 1 | Occupancy.occupied => -1
def localHamiltonianEigenvalue (p : ℕ) (o : Occupancy) : ℝ := 0

theorem h_prod_test (P : Finset ℕ) (s : ℝ) :
    (∑ ε : P → Occupancy,
      ∏ i : P, (localParityEigenvalue (ε i) *
        Real.exp (-s * localHamiltonianEigenvalue (i : ℕ) (ε i)))) =
    ∏ i : P, (∑ o : Occupancy, localParityEigenvalue o *
      Real.exp (-s * localHamiltonianEigenvalue (i : ℕ) o)) := by
  exact (Fintype.prod_sum (fun (i : P) (o : Occupancy) => localParityEigenvalue o * Real.exp (-s * localHamiltonianEigenvalue (i : ℕ) o))).symm
