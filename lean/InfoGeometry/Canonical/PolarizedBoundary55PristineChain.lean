import InfoGeometry.Algebra.Zorn.PolarizedQuadraticExtension55
import InfoGeometry.Geometry.PolarizedBoundaryBivectors

/-! Focused chain from the corrected quadratic extension to native Clifford and
exterior readouts.  No topological or field-theoretic conclusion is added. -/

noncomputable section

namespace InfoGeometry.Canonical.PolarizedBoundary55PristineChain

open InfoGeometry.Clifford.PolarizedMinkowski55
open InfoGeometry.Algebra.Zorn.PolarizedQuadraticExtension55
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Geometry.PolarizedBoundaryBivectors
open InfoGeometry.Canonical.HodgeStar4DFinite

theorem source_involution_packet (z : Boundary55) :
    boundaryQuadratic (mixedSwap z) = boundaryQuadratic z ∧
      mixedSwap (mixedSwap z) = z :=
  ⟨InfoGeometry.Clifford.PolarizedBoundaryInvolutions.mixedSwap_preserves z,
    InfoGeometry.Clifford.PolarizedBoundaryInvolutions.mixedSwap_sq z⟩

theorem boundary_chiral_packet (z : Boundary55) :
    selfDualPart (bivectorReadout (boundaryBivector z)) +
        antiSelfDualPart (bivectorReadout (boundaryBivector z)) =
          bivectorReadout (boundaryBivector z) ∧
      bivectorReadout (boundaryBivector (mixedSwap z)) =
        -bivectorReadout (boundaryBivector z) :=
  ⟨bivector_chiral_reconstruction _, mixedSwap_bivector z⟩

end InfoGeometry.Canonical.PolarizedBoundary55PristineChain
