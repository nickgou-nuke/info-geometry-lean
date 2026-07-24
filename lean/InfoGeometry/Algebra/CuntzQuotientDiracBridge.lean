import InfoGeometry.Algebra.CuntzN
import InfoGeometry.Algebra.CuntzSupergradedSUSY
import InfoGeometry.Algebra.CuntzPrimonHamiltonian

/-!
# Cuntz quotient as an abstract Cuntz-N algebra with Hodge-Dirac

This file connects the canonical tensor-algebra/RingQuot Cuntz owner to the
abstract `CuntzNAlgebra` interface from `CuntzN.lean`.

The main finite result says that the abstract Hodge-Dirac operator of the
quotient Cuntz algebra is exactly the sum of the quotient Majorana-type
supercharges `Sᵢ + Sᵢ†`, is self-adjoint, and has the expected range-projector
law.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzQuotientDiracBridge

open scoped BigOperators
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.SupergradedSUSY
open InfoGeometry.Algebra.CuntzPrimonHamiltonian

/-- The tensor-quotient Cuntz algebra instantiates the abstract `CuntzNAlgebra`. -/
def quotientCuntzNAlgebra (n : ℕ) :
    InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := n) (CuntzAlg n) where
  S := cuntzS n
  isometry := by
    intro i j
    simpa [star_cuntzS] using cuntz_orthogonality n i j
  range_sum := by
    simpa [star_cuntzS] using cuntz_ranges_sum_one n

/-- Its abstract Hodge-Dirac is exactly the sum of quotient Majorana supercharges. -/
theorem quotient_hodgeDirac_eq_sum_majorana (n : ℕ) :
    InfoGeometry.Algebra.Cuntz.hodgeDirac (quotientCuntzNAlgebra n) =
      ∑ i : Fin n, cuntzMajoranaSupercharge n i := by
  simp [InfoGeometry.Algebra.Cuntz.hodgeDirac, InfoGeometry.Algebra.Cuntz.finiteDirac,
    quotientCuntzNAlgebra, cuntzMajoranaSupercharge, star_cuntzS]

/-- The quotient Hodge-Dirac is self-adjoint. -/
theorem quotient_hodgeDirac_self_adjoint (n : ℕ) :
    star (InfoGeometry.Algebra.Cuntz.hodgeDirac (quotientCuntzNAlgebra n)) =
      InfoGeometry.Algebra.Cuntz.hodgeDirac (quotientCuntzNAlgebra n) := by
  exact InfoGeometry.Algebra.Cuntz.hodge_dirac_self_adjoint (O := quotientCuntzNAlgebra n)

/-- Abstract range projectors are exactly the quotient Cuntz primon projectors. -/
theorem quotient_range_projector_eq_primon_P (n : ℕ) (i : Fin n) :
    (quotientCuntzNAlgebra n).S i * star ((quotientCuntzNAlgebra n).S i) =
      P n i := by
  simp [quotientCuntzNAlgebra, P, star_cuntzS]

/-- Abstract range-projector idempotence specializes to the primon projector. -/
theorem quotient_primon_projector_idempotent_via_CuntzN (n : ℕ) (i : Fin n) :
    P n i * P n i = P n i := by
  simpa [quotient_range_projector_eq_primon_P n i] using
    InfoGeometry.Algebra.Cuntz.range_projection_idempotent (O := quotientCuntzNAlgebra n) i

/-- Packet: quotient CuntzN, Hodge-Dirac Majorana sum, self-adjointness, and projector law. -/
theorem finite_quotient_cuntzN_dirac_packet (n : ℕ) (i : Fin n) :
    InfoGeometry.Algebra.Cuntz.hodgeDirac (quotientCuntzNAlgebra n) =
        ∑ j : Fin n, cuntzMajoranaSupercharge n j ∧
    star (InfoGeometry.Algebra.Cuntz.hodgeDirac (quotientCuntzNAlgebra n)) =
        InfoGeometry.Algebra.Cuntz.hodgeDirac (quotientCuntzNAlgebra n) ∧
    (quotientCuntzNAlgebra n).S i * star ((quotientCuntzNAlgebra n).S i) =
        P n i ∧
    P n i * P n i = P n i := by
  exact ⟨quotient_hodgeDirac_eq_sum_majorana n,
    quotient_hodgeDirac_self_adjoint n,
    quotient_range_projector_eq_primon_P n i,
    quotient_primon_projector_idempotent_via_CuntzN n i⟩

end InfoGeometry.Algebra.CuntzQuotientDiracBridge

end noncomputable section
