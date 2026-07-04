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

abbrev zorn_tkk_e_plus_minus_anomaly_cancellation :=
  InfoGeometry.Physics.ZornTkkAnomalyCancellation.tkk_e_plus_minus_anomaly_cancellation

abbrev zorn_tkk_commutator_trace_evaluation :=
  InfoGeometry.Physics.ZornTkkAnomalyCancellation.tkk_commutator_trace_evaluation

abbrev brillouin_glide_conjugates_to_inverse :=
  InfoGeometry.Physics.KleinBottleCosmology.brillouin_glide_conjugates_to_inverse

abbrev brillouin_boundary_word :=
  InfoGeometry.Physics.KleinBottleCosmology.brillouin_boundary_word

abbrev pin55_glide_square_eq_translation :=
  InfoGeometry.Physics.KleinBottleCosmology.pin55_glide_square_eq_translation

abbrev finite_glide_orbit_charge_cancellation_packet :=
  InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal.finite_glide_orbit_charge_cancellation_packet

abbrev glideFlip_involutive :=
  InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal.glideFlip_involutive

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

abbrev projective_klein_formula_packet :=
  InfoGeometry.Topology.ProjectiveKleinCompactification.projective_klein_formula_packet

abbrev brillouin_klein_bottle_manifold_packet :=
  InfoGeometry.Topology.BrillouinKleinBottleManifold.brillouin_klein_bottle_manifold_packet

abbrev brillouin_klein_wallpaper_cross_section_packet :=
  InfoGeometry.Topology.BrillouinKleinBottleManifold.brillouin_klein_wallpaper_cross_section_packet

abbrev klein_bottle_cosmology_packet :=
  InfoGeometry.Physics.KleinBottleCosmology.klein_bottle_cosmology_packet

end InfoGeometry.Physics.KleinTransitionGlideSkeleton
