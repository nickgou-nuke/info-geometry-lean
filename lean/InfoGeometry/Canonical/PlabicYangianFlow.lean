import Mathlib
import InfoGeometry.Topology.PlabicBoundaryMeasurement

/-!
# Arbitrary-length bilocal boundary flow

The finite three- and four-charge cases live in
`Topology.PlabicBoundaryMeasurement`.  This file extends that owner with the
exact boundary-term formula for lists of arbitrary length.  It is an identity
for commutators in an associative ring, not a model of a graph mutation or a
full Yangian representation.
-/

namespace PlabicBoundaryMeasurement

variable {A : Type*} [Ring A]

/-- Total charge of a finite ordered list. -/
def chargeSum : List A → A
  | [] => 0
  | x :: xs => x + chargeSum xs

/-- Ordered bilocal commutator sum for a finite list of charges. -/
def bilocalList : List A → A
  | [] => 0
  | x :: xs => bilocalList xs + lieBracket x (chargeSum xs)

@[simp] theorem chargeSum_append (xs ys : List A) :
    chargeSum (xs ++ ys) = chargeSum xs + chargeSum ys := by
  induction xs with
  | nil => simp [chargeSum]
  | cons x xs ih => simp [chargeSum, ih, add_assoc]

/-- Concatenating two ordered blocks adds their internal bilocal sums and
the commutator of their total charges. -/
theorem bilocalList_append (xs ys : List A) :
    bilocalList (xs ++ ys) =
      bilocalList xs + bilocalList ys +
        lieBracket (chargeSum xs) (chargeSum ys) := by
  induction xs with
  | nil => simp [bilocalList, chargeSum, lieBracket]
  | cons x xs ih =>
      change bilocalList (xs ++ ys) +
          lieBracket x (chargeSum (xs ++ ys)) =
        (bilocalList xs + lieBracket x (chargeSum xs)) + bilocalList ys +
          lieBracket (x + chargeSum xs) (chargeSum ys)
      rw [ih, chargeSum_append]
      dsimp [lieBracket]
      noncomm_ring

/-- Moving the first charge to the end changes the ordered bilocal sum by
exactly twice the boundary commutator. -/
theorem bilocalList_cyclic_difference (x : A) (xs : List A) :
    bilocalList (xs ++ [x]) - bilocalList (x :: xs) =
      2 * lieBracket (chargeSum xs) x := by
  rw [bilocalList_append]
  simp [bilocalList, chargeSum, lieBracket]
  noncomm_ring

/-- On the zero-total-charge locus, moving the first charge to the end leaves
the bilocal commutator sum unchanged. -/
theorem bilocalList_cyclic_invariant (x : A) (xs : List A)
    (h : chargeSum (x :: xs) = 0) :
    bilocalList (xs ++ [x]) = bilocalList (x :: xs) := by
  have htail : chargeSum xs = -x := by
    dsimp [chargeSum] at h
    have h' : chargeSum xs + x = 0 := by simpa [add_comm] using h
    exact eq_neg_of_add_eq_zero_left h'
  have hdiff := bilocalList_cyclic_difference x xs
  rw [htail] at hdiff
  have hzero : 2 * lieBracket (-x) x = 0 := by
    dsimp [lieBracket]
    noncomm_ring
  have hEq : bilocalList (xs ++ [x]) - bilocalList (x :: xs) = 0 := by
    calc
      bilocalList (xs ++ [x]) - bilocalList (x :: xs) =
          2 * lieBracket (-x) x := hdiff
      _ = 0 := hzero
  exact sub_eq_zero.mp hEq

end PlabicBoundaryMeasurement
