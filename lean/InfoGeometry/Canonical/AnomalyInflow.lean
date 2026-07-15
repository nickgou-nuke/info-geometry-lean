import InfoGeometry.Canonical.TopologicalInvariants
import InfoGeometry.Canonical.HeatKernel
set_option linter.unusedVariables false

namespace AnomalyInflow

open TopologicalInvariants
open HeatKernel
open SpectralInference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Variation of the Chern-Simons term under a localized belief update.
This is the bulk topological response encoded by the loop-level Chern-Simons
term from the information connection.
-/
noncomputable def variationChernSimons (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  informationChernSimons L IST

/-- Canonical naming alias for the bulk Chern-Simons variation. -/
noncomputable abbrev bulkChernSimonsVariation
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  variationChernSimons L IST

/--
Reduced boundary spectral defect in the collapsed heat-kernel proxy layer.
In this model the boundary term is the sum of the first two reduced spectral
coefficients.
-/
noncomputable def boundaryAnomaly (_L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  a0 IST + a1 IST

/-- Canonical naming alias for the boundary anomaly density term. -/
noncomputable abbrev boundaryAnomalyDensity
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) : ℝ :=
  boundaryAnomaly L IST

/--
Canonical closure package for anomaly inflow in the reduced spectral proxy
model. The closure is derived under the flat-loop Chern-Simons hypothesis from
`TopologicalInvariants`.
-/
def AnomalyInflowClosure (L : BayesianLoop E) (IST : InfoSpectralTriple E) : Prop :=
  ∀ hFlat : IST.H.potential = fun x => (1 / 2 : ℝ) * inner ℝ x x,
    bulkChernSimonsVariation L IST + boundaryAnomaly L IST = 0

omit [FiniteDimensional ℝ E] in
@[simp] theorem boundaryAnomaly_eq_zero
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) :
    boundaryAnomaly L IST = 0 := by
  simp [boundaryAnomaly, a0_eq_spectralLogVolume, a1_eq_neg_spectralLogVolume]

omit [FiniteDimensional ℝ E] in
/--
The reduced inflow identity:
if the loop-level Chern-Simons term vanishes on a flat information
manifold, then the bulk variation is canceled by the reduced boundary spectral
defect.
-/
@[blueprint "thm:anomaly-inflow-cancellation"]
theorem anomaly_inflow_cancellation
    (L : BayesianLoop E) (IST : InfoSpectralTriple E)
    (hFlat : IST.H.potential = fun x => (1 / 2 : ℝ) * inner ℝ x x) :
    variationChernSimons L IST + boundaryAnomaly L IST = 0 := by
  calc
    variationChernSimons L IST + boundaryAnomaly L IST
        = informationChernSimons L IST + boundaryAnomaly L IST := by
            rfl
    _ = 0 + boundaryAnomaly L IST := by
          rw [cs_invariant_of_flat (L := L) (IST := IST) hFlat]
    _ = 0 := by simp [boundaryAnomaly_eq_zero]

omit [FiniteDimensional ℝ E] in
/-- Theorem `anomalyInflowClosure`. -/
theorem anomalyInflowClosure
    (L : BayesianLoop E) (IST : InfoSpectralTriple E) :
    AnomalyInflowClosure L IST := by
  intro _hFlat
  simpa [AnomalyInflowClosure, bulkChernSimonsVariation] using
    anomaly_inflow_cancellation (E := E) L IST _hFlat

end AnomalyInflow
