import InfoGeometry.Algebra.Grothendieck
import InfoGeometry.Projective.KleinQuadric
import InfoGeometry.Geometry.GromovHyperbolicity

/-!
# Polynomial geometry thread bridge

This is a witness-level integration surface for three existing finite owners:

* additive Grothendieck completion;
* the Plücker/Klein quadratic boundary;
* finite Gromov-product hyperbolicity.

The structure deliberately does not assert that these constructions are
equivalent, nor does it introduce motives, schemes, or Gromov--Witten
moduli.  It records the extra compatibility data needed before such a bridge
could be strengthened.
-/

namespace InfoGeometry.Canonical.PolynomialGeometryThreadBridge

open InfoGeometry.Projective.KleinQuadric
open InfoGeometry.Geometry.GromovHyperbolicity

noncomputable section

variable {M R X V : Type*}

/-- A finite, theorem-honest packet joining the three existing owner layers. -/
structure ThreadPacket
    [AddCommMonoid M] [CommRing R]
    [PseudoMetricSpace X] [AddCommGroup V] [Module R V] where
  classMap : Grothendieck M →+ R
  pluckerPoint : Plucker6 R
  pluckerBoundary : pluckerPoint.IsKlein
  metricSubset : Set X
  metricDelta : ℝ
  metricHyperbolic : GromovHyperbolicSubset metricDelta metricSubset
  projectorPos : V →ₗ[R] V
  projectorZero : V →ₗ[R] V
  projectorNeg : V →ₗ[R] V
  projectorReconstruction :
    projectorPos + projectorZero + projectorNeg = (LinearMap.id : V →ₗ[R] V)

/-!
## Transport laws already available from the owner files
-/

theorem scaled_boundary
    [AddCommMonoid M] [CommRing R]
    [PseudoMetricSpace X] [AddCommGroup V] [Module R V]
    (P : @ThreadPacket M R X V _ _ _ _ _)
    (a : R) :
    (Plucker6.scale a P.pluckerPoint).IsKlein := by
  exact Plucker6.isKlein_scale_of a P.pluckerPoint P.pluckerBoundary

theorem grothendieck_class_readback
    [AddCommMonoid M] [CommRing R]
    [PseudoMetricSpace X] [AddCommGroup V] [Module R V]
    (P : @ThreadPacket M R X V _ _ _ _ _)
    (f : M →+ R)
    (h : ∀ m, P.classMap (grothendieckMap M m) = f m)
    (x : Grothendieck M) :
    P.classMap x = grothendieckLift f x := by
  exact grothendieckLift_unique f P.classMap h x

theorem gromov_boundary_and_projector_reconstruction
    [AddCommMonoid M] [CommRing R]
    [PseudoMetricSpace X] [AddCommGroup V] [Module R V]
    (P : @ThreadPacket M R X V _ _ _ _ _ ) :
    P.pluckerPoint.IsKlein ∧
      GromovHyperbolicSubset P.metricDelta P.metricSubset ∧
    P.projectorPos + P.projectorZero + P.projectorNeg = (LinearMap.id : V →ₗ[R] V) := by
  exact ⟨P.pluckerBoundary, P.metricHyperbolic, P.projectorReconstruction⟩

/-!
## The explicit missing interface

The following record is intentionally only a contract.  A future owner may
populate it with a genuine map from a Peirce/projector carrier to Plücker
coordinates and prove that the map preserves the Klein polynomial.  Until
then, the compatibility is a field rather than an unjustified theorem.
-/

structure PolynomialBoundaryReadout
    [CommRing R] [AddCommGroup V] [Module R V] where
  toPlucker : V → Plucker6 R
  preservesBoundary : ∀ v, (toPlucker v).IsKlein

theorem readout_scaled_boundary
    [CommRing R] [AddCommGroup V] [Module R V]
    (B : PolynomialBoundaryReadout (R := R) (V := V))
    (v : V) (a : R) :
    (Plucker6.scale a (B.toPlucker v)).IsKlein := by
  exact Plucker6.isKlein_scale_of a (B.toPlucker v) (B.preservesBoundary v)

end
end InfoGeometry.Canonical.PolynomialGeometryThreadBridge
