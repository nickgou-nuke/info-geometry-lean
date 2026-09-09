import InfoGeometry.Topology.BuresWassersteinTransportTopCat

/-!
# A concrete metric backend on the readout interval

This is an honest finite-dimensional backend for the abstract
`BuresWassersteinDatum` interface.  It uses the subtype metric on `[0,1]`;
it is not claimed to be the Wasserstein distance between measures.
-/

noncomputable section

namespace InfoGeometry.Topology.UnitIntervalEuclideanTransportBackend

open InfoGeometry.Thermo.BuresWassersteinKMSCost
open InfoGeometry.Topology.BuresWassersteinTransportTopCat

abbrev UnitInterval := Set.Icc (0 : ℝ) 1
def unitIntervalDomain : PositiveStateDomain ℝ := ⟨UnitInterval⟩

def unitIntervalEuclideanDatum :
    BuresWassersteinDatum ℝ (Ω := unitIntervalDomain) where
  dist := fun ρ σ => dist ρ.val σ.val
  squaredDist := fun ρ σ => dist ρ.val σ.val ^ 2
  dist_nonneg := by
    intro ρ σ
    exact dist_nonneg
  squaredDist_nonneg := by
    intro ρ σ
    exact sq_nonneg _
  dist_self := by
    intro ρ
    exact dist_self ρ.val
  squaredDist_self := by
    intro ρ
    rw [dist_self]
    simp

theorem unitIntervalEuclideanDatum_squaredDist_continuous :
    Continuous (fun p : PositiveState unitIntervalDomain × PositiveState unitIntervalDomain =>
      unitIntervalEuclideanDatum.squaredDist p.1 p.2) := by
  have hval : Continuous (fun ρ : PositiveState unitIntervalDomain =>
      (ρ.val : ℝ)) := continuous_positiveState_val
  simpa [unitIntervalEuclideanDatum] using
    (continuous_dist.comp
      ((hval.comp continuous_fst).prodMk (hval.comp continuous_snd))).pow 2

theorem unitIntervalEuclideanDatum_dist_continuous :
    Continuous (fun p : PositiveState unitIntervalDomain × PositiveState unitIntervalDomain =>
      unitIntervalEuclideanDatum.dist p.1 p.2) := by
  have hval : Continuous (fun ρ : PositiveState unitIntervalDomain =>
      (ρ.val : ℝ)) := continuous_positiveState_val
  simpa [unitIntervalEuclideanDatum] using
    continuous_dist.comp
      ((hval.comp continuous_fst).prodMk (hval.comp continuous_snd))

end InfoGeometry.Topology.UnitIntervalEuclideanTransportBackend
