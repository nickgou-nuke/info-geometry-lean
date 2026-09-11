import InfoGeometry.SuperMetriplectic.CasimirHessianFisherBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Noncommutative metriplectic Casimir/Fisher bridge

The scalar coordinate-plane implementation formerly placed in this module is
not a Casimir theorem for an observable algebra.  The canonical owner is
`CasimirHessianFisherBridge`: a verified quadratic Casimir is an element of a
`CStarAlgebra`, its invariance is expressed by inner modular derivations, and
Fisher positivity is obtained from a positive functional and its native GNS
representation.

This file is a small importable bridge to those operatorial theorems.  It
introduces no coordinate bracket, diagonal metric, or scalar attractor claim.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace InfoGeometry.SuperMetriplectic.MetriplecticCasimirCommutationBridge

open InfoGeometry.SuperMetriplectic.CasimirHessianFisher
open InfoGeometry.OperatorAlgebra.ConstructiveCasimir

universe u v

variable {A : Type u} {ι : Type v} [Fintype ι]
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem casimir_is_central
    (D : NoncommutativeCasimirFisherData A ι) :
    IsCentral D.casimirElement :=
  D.casimirElement_isCentral

theorem casimir_modular_derivation_zero
    (D : NoncommutativeCasimirFisherData A ι) (H : A) :
    modularDerivation H D.casimirElement = 0 :=
  D.modularDerivation_casimir_zero H

theorem fisher_quadratic_nonneg
    (D : NoncommutativeCasimirFisherData A ι) (a : A) :
    0 ≤ D.fisherQuadratic a :=
  D.fisherQuadratic_nonneg a

theorem gns_fisher_quadratic_nonneg
    (D : NoncommutativeCasimirFisherData A ι) (a : A) :
    0 ≤
      (⟪InfoGeometry.Algebra.CuntzNativeGNSBridge.gnsVacuum D.state,
        InfoGeometry.Algebra.CuntzNativeGNSBridge.cuntzGNSRepresentation D.state
          (star a * a)
          (InfoGeometry.Algebra.CuntzNativeGNSBridge.gnsVacuum D.state)⟫_ℂ).re :=
  D.gns_fisherQuadratic_nonneg a

end InfoGeometry.SuperMetriplectic.MetriplecticCasimirCommutationBridge
