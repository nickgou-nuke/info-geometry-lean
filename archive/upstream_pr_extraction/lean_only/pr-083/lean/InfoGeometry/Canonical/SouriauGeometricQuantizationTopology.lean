import InfoGeometry.Canonical.SouriauGeometricQuantizationCore
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Topological carrier for the finite Souriau/prequantum core

The concrete plane and the trivial line/frame bundles inherit Mathlib's product
topologies.  This owner proves the continuity statements needed before any
smooth-manifold or non-trivial bundle construction is attempted.
-/

namespace InfoGeometry.Canonical

section TopologicalCarrier

instance : TopologicalSpace SymplecticPlane := inferInstance

noncomputable instance : TopologicalSpace (trivialLineTotal SymplecticPlane) :=
  inferInstanceAs (TopologicalSpace (SymplecticPlane × ℂ))

noncomputable instance : TopologicalSpace (trivialFrameTotal SymplecticPlane) :=
  inferInstanceAs (TopologicalSpace (SymplecticPlane × Circle))

theorem continuous_standardPlanePoint :
    Continuous (standardSymplecticPlaneLeaf.point) :=
  continuous_id

theorem continuous_trivialLineProjection :
    Continuous (trivialLineProjection : trivialLineTotal SymplecticPlane →
      SymplecticPlane) :=
  continuous_fst

theorem continuous_trivialFrameProjection :
    Continuous (trivialFrameProjection : trivialFrameTotal SymplecticPlane →
      SymplecticPlane) :=
  continuous_fst

theorem continuous_trivialFrameAction (u : Circle) :
    Continuous (fun p : trivialFrameTotal SymplecticPlane =>
      trivialFrameAction p u) := by
  exact continuous_fst.prodMk (continuous_snd.mul continuous_const)

theorem continuous_trivialFrameAction_pair :
    Continuous (fun p : trivialFrameTotal SymplecticPlane =>
      trivialFrameAction p p.2) := by
  exact continuous_fst.prodMk (continuous_snd.mul continuous_snd)

end TopologicalCarrier

end InfoGeometry.Canonical
