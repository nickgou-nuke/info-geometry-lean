import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# Malcev identity for the native split-octonion commutator

The commutator of the explicit alternative Zorn product is not Lie in
general.  This owner records the stronger Malcev identity directly on the
native element carrier, without installing a Lie algebra instance.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

def malcevDefect (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  sub
    (commutatorJacobiator X Y (commutator X Z))
    (commutator (commutatorJacobiator X Y Z) X)

set_option maxHeartbeats 10000000 in
theorem malcev_identity (X Y Z : ZornVectorMatrix R) :
    malcevDefect X Y Z = zero := by
  ext i
  · simp [malcevDefect, commutatorJacobiator, commutator, sub, add, neg,
      zero, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring_nf
  · fin_cases i <;>
      simp [malcevDefect, commutatorJacobiator, commutator, sub, add, neg,
        zero, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring_nf
  · fin_cases i <;>
      simp [malcevDefect, commutatorJacobiator, commutator, sub, add, neg,
        zero, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring_nf
  · simp [malcevDefect, commutatorJacobiator, commutator, sub, add, neg,
      zero, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring_nf

end InfoGeometry.Algebra.ZornVectorMatrix
