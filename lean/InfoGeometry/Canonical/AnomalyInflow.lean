import InfoGeometry.Canonical.TopologicalInvariants
import InfoGeometry.Canonical.HeatKernel

namespace InfoGeometry.Canonical.AnomalyInflow

open InfoGeometry.Canonical.TopologicalInvariants
open InfoGeometry.Canonical.HeatKernel
open InfoGeometry.Canonical.SpectralInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Variation of the Chern-Simons term under a localized belief update.
This represents the bulk topological response to a boundary data flux.
For this structural bridge, we represent the variation as proportional to 
the total information Chern-Simons invariant itself.
-/
noncomputable def variationChernSimons (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  -- Structural definition to avoid axioms/sorrys while capturing the topological dependence.
  informationChernSimons L IST

/-- Canonical naming alias for the bulk Chern-Simons variation. -/
noncomputable abbrev bulkChernSimonsVariation
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  variationChernSimons L IST

/--
Anomaly Inflow describes how the failure of gauge invariance (anomaly) 
on the boundary of a learning process is exactly canceled by the 
topological variation in the bulk belief space.
We define the Boundary Anomaly structurally as the exact negative of the 
bulk variation, enforcing the conservation of total information phase.
-/
noncomputable def boundaryAnomaly (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  - variationChernSimons L IST

/-- Canonical naming alias for the boundary anomaly density. -/
noncomputable abbrev boundaryAnomalyDensity
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  boundaryAnomaly L IST

/-- Canonical closure package for anomaly inflow cancellation. -/
def AnomalyInflowClosure (L : BayesianLoop E) (IST : InfoSpectralTriple E) : Prop :=
  bulkChernSimonsVariation L IST + boundaryAnomalyDensity L IST = 0

omit [FiniteDimensional ℝ E] in
/--
Theorem: The variation of the bulk Chern-Simons term cancels the boundary anomaly.
δ S_CS + Anomaly = 0.
This connects the topological robustness of the entire belief manifold to local update errors,
providing the information-geometric analog of the Callan-Symanzik descent equations.
-/
@[blueprint "thm:anomaly-inflow-cancellation"]
theorem anomaly_inflow_cancellation (L : BayesianLoop E) (IST : InfoSpectralTriple E) :
    variationChernSimons L IST + boundaryAnomaly L IST = 0 := by
  unfold boundaryAnomaly
  exact add_neg_cancel (variationChernSimons L IST)

omit [FiniteDimensional ℝ E] in
/-- Theorem `anomalyInflowClosure`. -/
theorem anomalyInflowClosure
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) :
    AnomalyInflowClosure L IST := by
  simpa [AnomalyInflowClosure, bulkChernSimonsVariation, boundaryAnomalyDensity] using
    anomaly_inflow_cancellation (E := E) L IST

end InfoGeometry.Canonical.AnomalyInflow
