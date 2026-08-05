import InfoGeometry.Algebra.CuntzNativeGNSBridge
import InfoGeometry.Algebra.CuntzGNSRepresentation
import InfoGeometry.Algebra.CuntzModularAutomorphism

/-!
# Native Cuntz GNS bridge

The algebraic `CuntzAlg` quotient is not given a fabricated C*-algebra or a
real `StarModule` instance.  A completed GNS carrier is therefore obtained
only from a genuine positive functional on an actual C*-algebra, together
with an existing Cuntz-family representation.  The algebraic quotient is
used solely as the source of that representation.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzModularAutomorphism
open InfoGeometry.Algebra.CuntzGNSRepresentation
open InfoGeometry.Algebra.CuntzNativeGNSBridge

namespace InfoGeometry.Canonical.CuntzGNSFilteredHilbertBridge

/-! ## Native completed GNS carrier -/

abbrev CuntzKMSGNSHilbert
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : A →ₚ[ℂ] ℂ) : Type _ := φ.GNS

theorem represented_cuntz_state_expectation_recovery
    {n : ℕ} {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (E : CuntzPositiveExtension n A)
    (x : CuntzAlg n) :
    ⟪gnsVacuum E.phi,
      cuntzGNSRepresentation E.phi
        (E.representation.toAlgHom x)
        (gnsVacuum E.phi)⟫_ℂ = E.omega x := by
  exact represented_cuntz_expectation_recovery E x

theorem represented_cuntz_state_cyclic
    {n : ℕ} {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (E : CuntzPositiveExtension n A) :
    DenseRange
      (fun a : A => cuntzGNSRepresentation E.phi a (gnsVacuum E.phi)) := by
  exact gnsVacuum_cyclic E.phi

/-! ## The diagonal is an actual Cuntz projector combination -/

@[simp] theorem sigma_diagonalElement_fixed
    (n : ℕ) (primes : Fin n → ℕ) (t : ℝ) (x : Fin n → ℂ) :
    sigma n primes t (diagonalElement n x) = diagonalElement n x := by
  simp [diagonalElement, sigma_fixes_projector]

end InfoGeometry.Canonical.CuntzGNSFilteredHilbertBridge
