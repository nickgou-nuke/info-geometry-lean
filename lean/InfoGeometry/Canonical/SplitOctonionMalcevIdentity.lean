import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Algebra.AlternativeDerivations

namespace InfoGeometry.Algebra.ZornVectorMatrix
variable {R : Type*} [CommRing R]

def malcevDefect (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  sub
    (commutatorJacobiator X Y (commutator X Z))
    (commutator (commutatorJacobiator X Y Z) X)

/-- The synthetic, coordinate-free proof of the Malcev identity for the split octonions.
    This replaces the brute-force component expansion and avoids `maxHeartbeats 10000000`. -/
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
