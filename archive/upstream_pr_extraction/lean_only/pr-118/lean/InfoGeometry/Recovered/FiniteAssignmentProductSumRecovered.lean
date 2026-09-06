import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Recovered.FiniteAssignmentProductSum

/--
A recovered finite-product expansion kernel from
`archive/scratch_recovery/test_sum_prod.lean`.

The archive file used a local two-state occupancy probe.  The reusable
mathematical content is the generic finite assignment identity: summing a
product over all assignments is the product of the local sums.
-/
theorem assignment_sum_eq_product_sum
    {ι α R : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [CommSemiring R]
    (F : ι → α → R) :
    (∑ ε : ι → α, ∏ i : ι, F i (ε i)) =
      ∏ i : ι, ∑ a : α, F i a := by
  exact (Fintype.prod_sum F).symm

/-- The recovered kernel specialized to a finite set of labels. -/
theorem finset_assignment_sum_eq_product_sum
    {ι α R : Type*} [DecidableEq ι] [Fintype α] [CommSemiring R]
    (P : Finset ι) (F : P → α → R) :
    (∑ ε : P → α, ∏ i : P, F i (ε i)) =
      ∏ i : P, ∑ a : α, F i a := by
  exact assignment_sum_eq_product_sum F

/-- Two-state occupancy used by the archived split-Majorana primon probe. -/
inductive Occupancy where
  | empty
  | occupied
  deriving DecidableEq, Fintype, Repr

/-- Local parity eigenvalue for the recovered two-state probe. -/
def localParityEigenvalue : Occupancy → ℝ
  | Occupancy.empty => 1
  | Occupancy.occupied => -1

/-- Abstract local Hamiltonian eigenvalue input for the recovered two-state probe. -/
abbrev LocalHamiltonianEigenvalue := ℕ → Occupancy → ℝ

/--
Recovered split-Majorana style finite product expansion.

Unlike the archive probe, this keeps the local Hamiltonian as explicit data
instead of hard-coding the zero Hamiltonian.
-/
theorem splitMajorana_twoState_assignment_sum
    (P : Finset ℕ) (s : ℝ) (H : LocalHamiltonianEigenvalue) :
    (∑ ε : P → Occupancy,
      ∏ i : P,
        localParityEigenvalue (ε i) * Real.exp (-s * H (i : ℕ) (ε i))) =
    ∏ i : P,
      ∑ o : Occupancy,
        localParityEigenvalue o * Real.exp (-s * H (i : ℕ) o) := by
  exact finset_assignment_sum_eq_product_sum P
    (fun i o => localParityEigenvalue o * Real.exp (-s * H (i : ℕ) o))

end InfoGeometry.Recovered.FiniteAssignmentProductSum
