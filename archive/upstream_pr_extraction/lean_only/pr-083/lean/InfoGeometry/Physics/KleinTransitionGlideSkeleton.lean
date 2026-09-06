import InfoGeometry.Physics.ZornTkkAnomalyCancellation
import InfoGeometry.Physics.KleinBottleCosmology
import InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal
import InfoGeometry.Topology.TwistedCohomologyWeyl
import InfoGeometry.Topology.BrillouinKleinBottleManifold
import InfoGeometry.Topology.ProjectiveKleinCompactification

namespace InfoGeometry.Physics.KleinTransitionGlideSkeleton

open InfoGeometry.Physics.ZornTkkAnomalyCancellation
open InfoGeometry.Physics.KleinBottleCosmology
open InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal
open InfoGeometry.Topology.Weyl
open InfoGeometry.Topology.BrillouinKleinBottleManifold
open InfoGeometry.Topology.ProjectiveKleinCompactification

theorem glide_odd_curvature_cancellation
    {BZ : Type*} [TopologicalSpace BZ]
    (gbz : InfoGeometry.Topology.Weyl.GlideBrillouinZone BZ)
    (ω : BZ → ℝ)
    (hω : InfoGeometry.Topology.Weyl.IsGlideOddCurvature gbz ω)
    (k : BZ) :
    ω k + ω (gbz.glide k) = (0 : ℝ) :=
  InfoGeometry.Topology.Weyl.glide_odd_curvature_cancellation gbz ω hω k


theorem berry_curvature_odd_cancellation
    {BZ : Type*} [TopologicalSpace BZ]
    (gbz : InfoGeometry.Topology.Weyl.GlideBrillouinZone BZ)
    (F : InfoGeometry.Topology.Weyl.TwistedBerryCurvature gbz)
    (k : BZ) :
    F.curvature k + F.curvature (gbz.glide k) = (0 : ℝ) :=
  InfoGeometry.Topology.Weyl.berry_curvature_odd_cancellation gbz F k


theorem induced_oddSheetBerryCurvature_owner_odd_cancellation
    {BZ : Type*} [TopologicalSpace BZ]
    (gbz : InfoGeometry.Topology.Weyl.GlideBrillouinZone BZ)
    (φ : BZ → ℝ)
    (s : InfoGeometry.Topology.Weyl.ChiralSheet)
    (k : BZ) :
    (InfoGeometry.Topology.Weyl.inducedSheetBerryCurvature gbz
      (InfoGeometry.Topology.Weyl.oddSheetConnection gbz φ)).curvature s k +
      (InfoGeometry.Topology.Weyl.inducedSheetBerryCurvature gbz
        (InfoGeometry.Topology.Weyl.oddSheetConnection gbz φ)).curvature s.swap
          (gbz.glide k) = 0 := by
  simpa using
    (InfoGeometry.Topology.Weyl.induced_oddSheetBerryCurvature_owner_odd_cancellation
      gbz φ s k)

end InfoGeometry.Physics.KleinTransitionGlideSkeleton
