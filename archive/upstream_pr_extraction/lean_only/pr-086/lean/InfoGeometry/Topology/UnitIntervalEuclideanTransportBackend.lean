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

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def unitIntervalEuclideanDatum :
    BuresWassersteinDatum ℝ (Ω := UnitInterval) where
  dist := fun ρ σ => dist ρ σ
  squaredDist := fun ρ σ => dist ρ σ ^ 2
  dist_nonneg := by
    intro ρ σ
    exact dist_nonneg
  squaredDist_nonneg := by
    intro ρ σ
    exact sq_nonneg _
  dist_self := by
    intro ρ
    exact dist_self ρ
  squaredDist_self := by
    intro ρ
    rw [dist_self]
    simp

theorem unitIntervalEuclideanDatum_squaredDist_continuous :
    Continuous (fun p : PositiveState UnitInterval × PositiveState UnitInterval =>
      unitIntervalEuclideanDatum.squaredDist p.1 p.2) := by
  exact continuous_dist.pow 2

theorem unitIntervalEuclideanDatum_dist_continuous :
    Continuous (fun p : PositiveState UnitInterval × PositiveState UnitInterval =>
      unitIntervalEuclideanDatum.dist p.1 p.2) := by
  exact continuous_dist

end InfoGeometry.Topology.UnitIntervalEuclideanTransportBackend
