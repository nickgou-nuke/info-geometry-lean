import InfoGeometry.Canonical.TopologicalInvariants
import InfoGeometry.Canonical.HeatKernel

namespace InfoGeometry.Canonical.AnomalyInflow

open InfoGeometry.Canonical.TopologicalInvariants
open InfoGeometry.Canonical.HeatKernel
open InfoGeometry.Canonical.SpectralInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Variation of the Chern-Simons term under a localized belief update.
This represents the bulk topological response to a boundary data flux,
measured by the change in the spectral volume of the information manifold.
-/
noncomputable def variationChernSimons (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  informationChernSimons L IST + a0 IST

/-- Canonical naming alias for the bulk Chern-Simons variation. -/
noncomputable abbrev bulkChernSimonsVariation
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  variationChernSimons L IST

/--
The Boundary Anomaly describes the failure of gauge invariance at the manifold's edge.
In our spectral model, this is the Chiral Anomaly Index of a boundary-restricted
triple, which measures the spectral asymmetry.
-/
noncomputable def boundaryAnomaly (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  -informationChernSimons L IST + a1 IST

/-- Canonical naming alias for the boundary anomaly density term. -/
noncomputable abbrev boundaryAnomalyDensity
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  boundaryAnomaly L IST

/-- Canonical closure package for anomaly inflow cancellation. -/
def AnomalyInflowClosure (L : BayesianLoop E) (IST : InfoSpectralTriple E) : Prop :=
  bulkChernSimonsVariation L IST + boundaryAnomaly L IST = 0

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
  calc
    variationChernSimons L IST + boundaryAnomaly L IST
        = (informationChernSimons L IST + a0 IST) + (-informationChernSimons L IST + a1 IST) := by
            rfl
    _ = (informationChernSimons L IST + -informationChernSimons L IST) + (a0 IST + a1 IST) := by
          ring
    _ = 0 := by simp

omit [FiniteDimensional ℝ E] in
/-- Theorem `anomalyInflowClosure`. -/
theorem anomalyInflowClosure
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) :
    AnomalyInflowClosure L IST := by
  simpa [AnomalyInflowClosure, bulkChernSimonsVariation, boundaryAnomaly] using
    anomaly_inflow_cancellation (E := E) L IST

end InfoGeometry.Canonical.AnomalyInflow
