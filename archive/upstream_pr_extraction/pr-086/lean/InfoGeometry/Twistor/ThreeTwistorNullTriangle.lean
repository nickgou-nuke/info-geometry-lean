import InfoGeometry.Twistor.NullParavectorTwistorFlags
import InfoGeometry.Twistor.TwoTwistorPluckerKlein

/-!
# Finite cyclic three-twistor null triangle

The vertices are existing null paravector/incidence flags.  Cyclicity is only
the finite `Fin 3` indexing of consecutive edges.  The owner records the
native Pluecker/Klein readout and does not add Hermitian reality or manifold
curvature assumptions.
-/

namespace InfoGeometry.Twistor.ThreeTwistorNullTriangle

open InfoGeometry.Twistor.NullParavectorTwistorFlags
open InfoGeometry.Twistor.TwoTwistorPluckerKlein
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6

structure Triangle where
  vertex : Fin 3 → BoundaryIncidenceFlag

def nextVertex (i : Fin 3) : Fin 3 := i + 1

noncomputable def edgePlucker (T : Triangle) (i : Fin 3) : Plucker6 ℂ :=
  twistorPairPlucker (T.vertex i).Z (T.vertex (nextVertex i)).Z

theorem vertex_null (T : Triangle) (i : Fin 3) :
    (T.vertex i).v.IsNull :=
  (T.vertex i).hv

theorem vertex_twistor_nonzero (T : Triangle) (i : Fin 3) :
    (T.vertex i).Z ≠ 0 := by
  exact BoundaryIncidenceFlag.nonzero_twistor (T.vertex i)

theorem edgePlucker_on_klein (T : Triangle) (i : Fin 3) :
    kleinQ (edgePlucker T i) = 0 := by
  exact twistorPairPlucker_on_klein
    (T.vertex i).Z (T.vertex (nextVertex i)).Z

theorem edgePlucker_reverse (T : Triangle) (i : Fin 3) :
    twistorPairPlucker (T.vertex (nextVertex i)).Z (T.vertex i).Z =
      Plucker6.scale (-1) (edgePlucker T i) := by
  exact twistorPairPlucker_swap
    (T.vertex i).Z (T.vertex (nextVertex i)).Z

end InfoGeometry.Twistor.ThreeTwistorNullTriangle
