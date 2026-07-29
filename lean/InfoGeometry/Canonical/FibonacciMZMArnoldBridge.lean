import InfoGeometry.Categorical.MTC_PentagonTriangle
import InfoGeometry.Core.MajoranaLiftPacket
import InfoGeometry.Topology.AmplituhedronBoundaryRank32

/-!
# Fibonacci, Majorana, and Arnold owner synthesis

All mathematical inputs are explicit. The Arnold component remains a full
labelled exterior-product realization, not only its carrier cardinality.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Categorical.MTC_PentagonTriangle
open InfoGeometry.Core
open InfoGeometry.Topology.AmplituhedronBoundary

theorem fibonacci_mzm_arnold_interface
    {R E : Type} [CommRing R]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (q : Units ℂ) (tau s : ℂ)
    (hsq : s ^ 2 = tau)
    (hTau : tau ^ 2 + tau = 1)
    (hArtin :
      MTC_RMatrix q * MTC_BMatrix q tau s * MTC_RMatrix q =
        MTC_BMatrix q tau s * MTC_RMatrix q * MTC_BMatrix q tau s)
    (arnold : ArnoldProductRank32Realization R) :
    (MTC_FusionMatrix tau s * MTC_FusionMatrix tau s = 1 ∧
      (MTC_FusionMatrix tau s).det = -1 ∧
      MTC_BMatrix q tau s =
        MTC_FusionMatrix tau s *
          MTC_RMatrix q *
            MTC_FusionMatrix tau s ∧
      MTC_RMatrix q * MTC_BMatrix q tau s * MTC_RMatrix q =
        MTC_BMatrix q tau s * MTC_RMatrix q * MTC_BMatrix q tau s)
      ∧
    ((canonicalMajoranaJ (E := E)).comp (canonicalMajoranaJ (E := E)) =
        ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) ∧
      (canonicalMajoranaEps (E := E)).comp (canonicalMajoranaEps (E := E)) =
        ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) ∧
      (canonicalMajoranaJ (E := E)).comp (canonicalMajoranaEps (E := E)) =
        -((canonicalMajoranaEps (E := E)).comp (canonicalMajoranaJ (E := E))) ∧
      (canonicalMajoranaK (E := E)).comp (canonicalMajoranaK (E := E)) =
        -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)))
      ∧
    (Fintype.card BoundaryRank32State = 32 ∧
      ∀ state : BoundaryRank32State,
        arnold.carrierReadout state =
          arnoldChannelProduct R (arnold.channel state)) := by
  exact ⟨MTC_FiniteShadow q tau s hsq hTau hArtin,
    canonicalMajorana_root_laws (E := E),
    ArnoldProductRank32Realization.label_card R arnold,
    arnold.carrier_eq_arnoldChannelProduct⟩

end InfoGeometry.Canonical
