import Mathlib
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SugawaraAlgebraicLemmas

Native algebraic lemmas for the Sugawara commutator calculus.

This module isolates the ring identities needed to expand commutators of
quadratic current terms. It does not introduce any VOA, OPE, or spectral
claims. The only content here is honest associative-ring algebra.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.SugawaraAlgebraicLemmas

variable {Op : Type*} [Ring Op]

/-- Standard commutator in an associative ring. -/
@[rep_depth operator]
def comm (A B : Op) : Op :=
  A * B - B * A

/-- `comm (A * B) C = A * comm B C + comm A C * B`. -/
@[rep_depth operator]
theorem comm_mul_left (A B C : Op) :
    comm (A * B) C = A * comm B C + comm A C * B := by
  unfold comm
  noncomm_ring

/-- `comm A (B * C) = comm A B * C + B * comm A C`. -/
@[rep_depth operator]
theorem comm_mul_right (A B C : Op) :
    comm A (B * C) = comm A B * C + B * comm A C := by
  unfold comm
  noncomm_ring

/-- The commutator of an element with `0` vanishes. -/
@[rep_depth operator]
theorem comm_zero_right (A : Op) : comm A 0 = 0 := by
  unfold comm
  simp

/-- The commutator of `0` with any element vanishes. -/
@[rep_depth operator]
theorem zero_comm (A : Op) : comm 0 A = 0 := by
  unfold comm
  simp

/-- The commutator of an element with itself vanishes. -/
@[rep_depth operator]
theorem comm_self (A : Op) : comm A A = 0 := by
  unfold comm
  simp

/-- The commutator distributes over a finite sum on the left. -/
@[rep_depth operator]
theorem comm_sum_left {ι : Type*} (s : Finset ι) (A : ι → Op) (B : Op) :
    comm (Finset.sum s A) B = Finset.sum s (fun i => comm (A i) B) := by
  unfold comm
  rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

/-- The commutator distributes over a finite sum on the right. -/
@[rep_depth operator]
theorem comm_sum_right {ι : Type*} (s : Finset ι) (A : Op) (B : ι → Op) :
    comm A (Finset.sum s B) = Finset.sum s (fun i => comm A (B i)) := by
  unfold comm
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

end InfoGeometry.Canonical.SugawaraAlgebraicLemmas
