import InfoGeometry.Canonical.PeirceProjectorGrothendieckClass
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Peirce projector additive readouts

The existing Peirce Grothendieck identity can be transported through any
additive homomorphism.  This is an additive readout theorem only: it does not
identify the target with a projective-module definition of `K₀`.
-/

namespace InfoGeometry.Topology.PeirceProjectorKTheoryBridge

open InfoGeometry.Physics.Algebra

variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {G : Type*} [AddCommGroup G]

theorem peirce_ktheory_readout_sum
    (φ : Grothendieck R →+ G) (T : R) :
    φ (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
        (projPos T)) +
      φ (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
        (projZero T)) +
      φ (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
        (projNeg T)) =
      φ (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
        (1 : R)) := by
  calc
    φ (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
        (projPos T)) +
        φ (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
          (projZero T)) +
        φ (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
          (projNeg T)) =
        φ (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
          (projPos T) +
          InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
            (projZero T) +
          InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
            (projNeg T)) := by
          rw [map_add, map_add]
    _ = φ (InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.classOf
        (1 : R)) := by
          rw [InfoGeometry.Canonical.PeirceProjectorGrothendieckClass.peirce_projector_class_sum]

end InfoGeometry.Topology.PeirceProjectorKTheoryBridge
