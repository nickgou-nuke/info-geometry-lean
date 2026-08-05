import InfoGeometry.Canonical.ZornVectorMatrixMöbiusAction
import InfoGeometry.Topology.ProjectiveBoundarySL2Action

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra
open InfoGeometry.Topology

variable {R : Type*} [CommRing R]

/-!
# Zorn boundary block to the unimodular projective boundary

The raw Zorn Möbius formula is retained in its original owner.  This adapter
connects its visible 2-by-2 block to the quotient-safe projective boundary,
but only under an explicit determinant-one hypothesis.
-/

def zornBoundaryBlock (Z : ZornVectorMatrix R) :
    Matrix (Fin 2) (Fin 2) R :=
  ![![Z.a, Z.v 0], ![Z.w 0, Z.b]]

def zornBoundarySL2
    (Z : ZornVectorMatrix R)
    (hdet : det2 (zornBoundaryBlock Z) = 1) :
    SL2BoundaryMatrix R where
  matrix := zornBoundaryBlock Z
  det_eq_one := hdet

def zornProjectiveBoundaryAction
    (Z : ZornVectorMatrix R)
    (hdet : det2 (zornBoundaryBlock Z) = 1) :
    ProjectiveBoundaryAction R :=
  (zornBoundarySL2 Z hdet).toProjectiveAction

def zornProjectiveBoundaryActionOnBoundary
    (Z : ZornVectorMatrix R)
    (hdet : det2 (zornBoundaryBlock Z) = 1) :
    Topology.ProjectiveBoundary R → Topology.ProjectiveBoundary R :=
  (zornProjectiveBoundaryAction Z hdet).onBoundary

@[simp] theorem zornProjectiveBoundaryActionOnBoundary_mk
    (Z : ZornVectorMatrix R)
    (hdet : det2 (zornBoundaryBlock Z) = 1)
    (p : Topology.UnimodularPair R) :
    zornProjectiveBoundaryActionOnBoundary Z hdet
        (Topology.projectiveBoundaryMk p) =
      Topology.projectiveBoundaryMk
        ((zornBoundarySL2 Z hdet).applyPair p) := rfl

end InfoGeometry.Canonical
