import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularFeasibleHomeomorph

/-!
# Topological readout of feasible symbolic-latent modular homeomorphisms

The feasible subtype already carries an actual modular homeomorphism for each
time parameter.  This owner packages the resulting orbit readout as a
topological map and records that the feasible orbit map is continuous.
No new dynamical law is introduced.
-/

namespace InfoGeometry.Topology.SymbolicLatentModularFeasibleHomeomorphTopological

noncomputable section

variable {X : Type*} [TopologicalSpace X]
variable {ι : Type*} [Fintype ι]

/-- The feasible orbit map associated to an observation-preserving modular flow. -/
def feasibleHomeomorphOrbitReadout
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ)
    (x : S.feasibleSet targets) : ℝ → S.feasibleSet targets :=
  fun t => Φ.feasibleHomeomorph targets t x

@[simp] theorem feasibleHomeomorphOrbitReadout_apply
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ)
    (x : S.feasibleSet targets) (t : ℝ) :
    feasibleHomeomorphOrbitReadout Φ targets x t =
      Φ.feasibleHomeomorph targets t x :=
  rfl

/-- The feasible orbit readout at time zero is the identity. -/
theorem feasibleHomeomorphOrbitReadout_zero
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ)
    (x : S.feasibleSet targets) :
    feasibleHomeomorphOrbitReadout Φ targets x 0 = x := by
  simpa [feasibleHomeomorphOrbitReadout] using
    (Φ.feasibleHomeomorph_zero_apply targets x)

/-- The feasible orbit readout is continuous in time for each feasible point. -/
theorem continuous_feasibleHomeomorphOrbitReadout
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (targets : ι → Set ℝ)
    (x : S.feasibleSet targets) :
    Continuous (feasibleHomeomorphOrbitReadout Φ targets x) := by
  exact Continuous.subtype_mk
    (Φ.toSymbolicLatentModularFlow.continuous_act.comp
      (continuous_id.prodMk continuous_const))
    (fun t => Φ.feasibleSet_preserved_forward targets t x.2)

end
end InfoGeometry.Topology.SymbolicLatentModularFeasibleHomeomorphTopological
