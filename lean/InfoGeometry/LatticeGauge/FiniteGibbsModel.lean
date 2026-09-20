import InfoGeometry.LatticeGauge.FinitePlaquette
import InfoGeometry.Probability.FiniteGibbsDeformationReadout

noncomputable section

namespace InfoGeometry.LatticeGauge

open InfoGeometry.Probability.FiniteGibbsDeformationReadout

variable {Vertex Edge Face Gauge : Type*}
variable [Fintype Edge] [DecidableEq Edge] [Fintype Face]
variable [Group Gauge] [Fintype Gauge] [DecidableEq Gauge]

def equilibriumWeight (lattice : PlaquetteLattice Vertex Edge Face) (beta : ℝ) :
    Configuration Edge Gauge → ℝ :=
  gibbsDistribution (plaquetteAction lattice) beta

theorem partition_pos (lattice : PlaquetteLattice Vertex Edge Face) (beta : ℝ) :
    0 < gibbsPartition (plaquetteAction lattice (Gauge := Gauge)) beta :=
  gibbsPartition_pos _ beta

theorem equilibriumWeight_pos (lattice : PlaquetteLattice Vertex Edge Face) (beta : ℝ)
    (links : Configuration Edge Gauge) :
    0 < equilibriumWeight lattice beta links := by
  change 0 < gibbsWeight (plaquetteAction lattice) beta links /
    gibbsPartition (plaquetteAction lattice) beta
  exact div_pos (gibbsWeight_pos _ beta links) (partition_pos lattice beta)

theorem equilibriumWeight_sum_one (lattice : PlaquetteLattice Vertex Edge Face) (beta : ℝ) :
    ∑ links : Configuration Edge Gauge, equilibriumWeight lattice beta links = 1 :=
  sum_gibbsDistribution _ beta

theorem equilibriumWeight_gauge_invariant (lattice : PlaquetteLattice Vertex Edge Face)
    (beta : ℝ) (gauge : Vertex → Gauge) (links : Configuration Edge Gauge) :
    equilibriumWeight lattice beta (gaugeTransform lattice gauge links) =
      equilibriumWeight lattice beta links := by
  change Real.exp (-beta * plaquetteAction lattice (gaugeTransform lattice gauge links)) /
      gibbsPartition (plaquetteAction lattice) beta =
    Real.exp (-beta * plaquetteAction lattice links) /
      gibbsPartition (plaquetteAction lattice) beta
  rw [plaquetteAction_gauge_invariant]

end InfoGeometry.LatticeGauge
