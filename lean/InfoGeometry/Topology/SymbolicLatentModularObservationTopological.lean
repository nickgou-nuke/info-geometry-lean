import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularObservation

/-!
# Topological readout of observation-preserving symbolic-latent modular flows

The native observation-preserving modular-flow structure already records the
orbit invariance of the finite symbolic readout.  This owner packages the
orbit readout as a topological map and records that it is constant along the
flow.  No new flow law, quotient, or probabilistic structure is introduced.
-/

namespace InfoGeometry.Topology.SymbolicLatentModularObservationTopological

noncomputable section

variable {X : Type*} [TopologicalSpace X]
variable {ι : Type*} [Fintype ι]

/-- The symbolic observation readout along a modular orbit. -/
def symbolicLatentObservableOrbitReadout
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (x : X) : ℝ → (ι → ℝ) :=
  fun t => S.obs (Φ.act t x)

@[simp] theorem symbolicLatentObservableOrbitReadout_apply
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (x : X) (t : ℝ) :
    symbolicLatentObservableOrbitReadout Φ x t = S.obs (Φ.act t x) :=
  rfl

/-- The orbit readout is constant because the flow preserves observations. -/
theorem symbolicLatentObservableOrbitReadout_eq_const
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (x : X) :
    symbolicLatentObservableOrbitReadout Φ x = fun _ : ℝ => S.obs x := by
  funext t
  exact Φ.preserves_observation t x

/-- The orbit readout is continuous. -/
theorem continuous_symbolicLatentObservableOrbitReadout
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (x : X) :
    Continuous (symbolicLatentObservableOrbitReadout Φ x) := by
  rw [symbolicLatentObservableOrbitReadout_eq_const]
  exact continuous_const

/-- The orbit readout is locally constant on the discrete time axis. -/
theorem isLocallyConstant_symbolicLatentObservableOrbitReadout
    {S : FiniteSymbolicLatentSystem X ι}
    (Φ : SymbolicLatentObservableModularFlow S)
    (x : X) :
    IsLocallyConstant (symbolicLatentObservableOrbitReadout Φ x) := by
  rw [symbolicLatentObservableOrbitReadout_eq_const]
  exact IsLocallyConstant.const (S.obs x)

end
end InfoGeometry.Topology.SymbolicLatentModularObservationTopological
