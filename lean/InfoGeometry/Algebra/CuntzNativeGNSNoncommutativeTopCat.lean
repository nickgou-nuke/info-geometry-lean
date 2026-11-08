import InfoGeometry.Algebra.CuntzNativeGNSTopologicalBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Noncommutative multiplication in the native GNS `TopCat` realization

The algebraic Cuntz/GNS owner supplies a genuine `StarAlgHom` into bounded
operators on a Hilbert completion.  This bridge records how its
noncommutative multiplication is seen by `TopCat`: multiplication in the
source becomes composition of the represented operators, with the categorical
order made explicit.  It introduces no diagonal or scalar surrogate.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace InfoGeometry.Algebra.CuntzNativeGNSNoncommutativeTopCat

open CategoryTheory
open InfoGeometry.Algebra.CuntzNativeGNSBridge
open InfoGeometry.Algebra.CuntzNativeGNSTopologicalBridge

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (φ : A →ₚ[ℂ] ℂ)

theorem gnsOperatorTopCat_mul (a b : A) :
    gnsOperatorTopCat φ (a * b) =
      gnsOperatorTopCat φ b ≫ gnsOperatorTopCat φ a := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change cuntzGNSRepresentation φ (a * b) x =
    cuntzGNSRepresentation φ a (cuntzGNSRepresentation φ b x)
  rw [map_mul]
  rfl

theorem gnsOperatorTopCat_commutator_apply (a b : A) (x : φ.GNS) :
    cuntzGNSRepresentation φ (a * b - b * a) x =
      cuntzGNSRepresentation φ a (cuntzGNSRepresentation φ b x) -
        cuntzGNSRepresentation φ b (cuntzGNSRepresentation φ a x) := by
  rw [map_sub, map_mul, map_mul]
  rfl

theorem gnsOperatorTopCat_commutes_of_commutes
    (a b : A) (h : a * b = b * a) :
    gnsOperatorTopCat φ a ≫ gnsOperatorTopCat φ b =
      gnsOperatorTopCat φ b ≫ gnsOperatorTopCat φ a := by
  rw [← gnsOperatorTopCat_mul φ b a, ← gnsOperatorTopCat_mul φ a b, h]

end InfoGeometry.Algebra.CuntzNativeGNSNoncommutativeTopCat
