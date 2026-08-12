import InfoGeometry.Projective.SplitCl44NullBoundary
import InfoGeometry.Canonical.BoundaryBraidRepresentation

/-!
# Marked configurations and braid-frame data over a projective null boundary

This owner supplies the missing typed interface between the projective null
boundary and the existing finite braid representation.  A `BoundarySurface`
is intentionally only an embedded carrier: no dimension, manifold, or Artin
braid-group assertion is made here.  Those hypotheses belong to a later
surface-specific owner.
-/

namespace InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge

open InfoGeometry.Projective.SplitCl44NullBoundary
open InfoGeometry.Canonical.BoundaryBraidRepresentation
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Physics.YangBaxterQSwap

abbrev BoundaryPoint := SplitCl44ProjectiveNullSpace

structure BoundarySurface where
  Point : Type*
  embed : Point → BoundaryPoint

def PairwiseDistinct {S : Type*} {N : ℕ} (x : Fin N → S) : Prop :=
  ∀ i j, i ≠ j → x i ≠ x j

def OrderedConfiguration (S : Type*) (N : ℕ) :=
  {x : Fin N → S // PairwiseDistinct x}

def MarkedPoint (S : BoundarySurface) := S.Point × Fin 3

def MarkedConfiguration (S : BoundarySurface) (N : ℕ) :=
  OrderedConfiguration (MarkedPoint S) N

def underlyingPoints {S : BoundarySurface} {N : ℕ}
    (x : MarkedConfiguration S N) : Fin N → S.Point :=
  fun i => (x.1 i).1

theorem markedConfiguration_pairwiseDistinct {S : BoundarySurface} {N : ℕ}
    (x : MarkedConfiguration S N) :
    PairwiseDistinct x.1 :=
  x.2

structure BoundaryBraidFrameRepresentation where
  representation : BoundaryBraidGroup →* BoundaryBraidCarrier

def canonicalBoundaryBraidFrameRepresentation :
    BoundaryBraidFrameRepresentation where
  representation := boundaryBraidRepresentation

theorem representation_map_mul
    (R : BoundaryBraidFrameRepresentation)
    (g h : BoundaryBraidGroup) :
    R.representation (g * h) =
      R.representation g * R.representation h := by
  exact R.representation.map_mul g h

theorem canonical_representation_artin :
    boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) *
        boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) *
        boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) =
      boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) *
        boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) *
        boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) := by
  exact boundaryBraidRepresentation_artin

end InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge
