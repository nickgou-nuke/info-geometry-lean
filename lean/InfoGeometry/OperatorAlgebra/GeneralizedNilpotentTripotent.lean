import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# Generic nilpotent and tripotent endomorphisms

The carrier in this file is an endomorphism algebra, not a diagonal matrix
model.  The tripotent projectors therefore act on an arbitrary module and all
polynomial identities are proved in the noncommutative endomorphism ring.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.GeneralizedNilpotentTripotent

section Tripotent

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Invertible (2 : R)]

abbrev EndM (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :=
  Module.End R M

/-- A tripotent endomorphism on an arbitrary module. -/
structure TripotentOperator where
  O : EndM R M
  h_tripotent : O * O * O = O

/-- The `+1` projector of a tripotent endomorphism. -/
noncomputable def projectPlus (t : TripotentOperator (R := R) (M := M)) : EndM R M :=
  (⅟ (2 : R)) • (t.O ^ 2 + t.O)

/-- The `-1` projector of a tripotent endomorphism. -/
noncomputable def projectMinus (t : TripotentOperator (R := R) (M := M)) : EndM R M :=
  (⅟ (2 : R)) • (t.O ^ 2 - t.O)

/-- The null projector of a tripotent endomorphism. -/
noncomputable def projectNull (t : TripotentOperator (R := R) (M := M)) : EndM R M :=
  1 - t.O ^ 2

lemma tripotent_pow_four (t : TripotentOperator (R := R) (M := M)) :
    t.O ^ 4 = t.O ^ 2 := by
  calc
    t.O ^ 4 = t.O ^ 3 * t.O := by rw [pow_succ]
    _ = (t.O * t.O * t.O) * t.O := by
      rfl
    _ = t.O * t.O := by rw [t.h_tripotent]
    _ = t.O ^ 2 := by rw [pow_two]

lemma tripotent_pow_three (t : TripotentOperator (R := R) (M := M)) :
    t.O ^ 3 = t.O := by
  simpa [pow_succ, pow_two, mul_assoc] using t.h_tripotent

/-- The active projectors reconstruct the square of the tripotent. -/
theorem active_projectors_sum (t : TripotentOperator (R := R) (M := M)) :
    projectPlus t + projectMinus t = t.O ^ 2 := by
  simp only [projectPlus, projectMinus]
  rw [← smul_add]
  rw [show (t.O ^ 2 + t.O) + (t.O ^ 2 - t.O) = (2 : R) • t.O ^ 2 by
    module]
  rw [smul_smul, invOf_mul_self]
  simp

/-- The three tripotent projectors form a partition of the identity. -/
theorem projector_sum_is_one (t : TripotentOperator (R := R) (M := M)) :
    projectPlus t + projectMinus t + projectNull t = 1 := by
  rw [active_projectors_sum]
  simp [projectNull]

/-- The tripotent is reconstructed from its signed sectors. -/
theorem operator_reconstruction (t : TripotentOperator (R := R) (M := M)) :
    t.O = projectPlus t - projectMinus t := by
  simp only [projectPlus, projectMinus]
  rw [← smul_sub]
  rw [show (t.O ^ 2 + t.O) - (t.O ^ 2 - t.O) = (2 : R) • t.O by
    module]
  rw [smul_smul, invOf_mul_self]
  simp

/-- The null projector is annihilated by the tripotent on the left. -/
theorem operator_mul_projectNull_eq_zero
    (t : TripotentOperator (R := R) (M := M)) :
    t.O * projectNull t = 0 := by
  simp only [projectNull]
  calc
    t.O * (1 - t.O ^ 2) = t.O - t.O ^ 3 := by noncomm_ring
    _ = 0 := by rw [tripotent_pow_three t]; abel

/-- Active support vanishing forces an arbitrary vector into the null sector. -/
theorem null_projector_smul_of_active_support_zero
    (t : TripotentOperator (R := R) (M := M)) (x : M)
    (h : (projectPlus t + projectMinus t) x = 0) :
    projectNull t x = x := by
  have hsum := congrArg (fun A : EndM R M => A x) (projector_sum_is_one t)
  simpa [map_add, h] using hsum

end Tripotent

section Nilpotent

/-- Universal finite geometric inverse for a nilpotent element of any ring. -/
theorem generalized_unipotent_inverse {A : Type*} [Ring A] {degree : ℕ}
    (X : A) (h : X ^ degree = 0) :
    (1 + X) * (∑ j ∈ Finset.range degree, (-1 : A) ^ j * X ^ j) = 1 := by
  have hsum : (∑ j ∈ Finset.range degree, (-1 : A) ^ j * X ^ j) =
      ∑ j ∈ Finset.range degree, (-X) ^ j := by
    simp [← neg_pow X]
  rw [hsum, ← sub_neg_eq_add, mul_neg_geom_sum (-X) degree]
  rw [neg_pow, h, mul_zero]
  simp

end Nilpotent

end InfoGeometry.OperatorAlgebra.GeneralizedNilpotentTripotent
