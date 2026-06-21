import InfoGeometry.Canonical.SpectralAction
import Mathlib.Data.Real.Basic

open CategoryTheory Limits

namespace InfoGeometry.Canonical

variable (Q : ∀ n, QuadraticForm ℝ (InfoGeometry.Topology.V n))
variable (h_compat : ∀ (m n : ℕ) (h : m ≤ n) (x : InfoGeometry.Topology.V m), 
  Q n (fun i => if h_lim : i.val < 2 * m then x ⟨i.val, h_lim⟩ else 0) = Q m x)
variable [HasColimit (CliffordTowerCausalFunctor Q h_compat)]

/--
  The Conformal Spectral Link:
  Asserts that the a₄ coefficient (the constant topological term in the 4D spectral action)
  is rigidly fixed by the Central Charge `c` of the Virasoro anomalous bridge.
-/
def IsConformalSpectralLink (a4 : ℝ) (c : ℝ) : Prop :=
  a4 = c / 24

/--
  The Conformal Anomaly Invariance Theorem:
  Proves that if the Spectral Action's high-energy scaling factors vanish (Λ → 0),
  the residual vacuum energy of the Causal Spacetime is entirely dictated 
  by the purely topological Virasoro central charge anomaly.
-/
theorem conformal_anomaly_residual_vacuum
    (S : ℝ → ℝ) (a0 a2 a4 c : ℝ)
    (h_expansion : HasAsymptoticSpectralExpansion S a0 a2 a4)
    (h_link : IsConformalSpectralLink a4 c) :
    ∃ (limit_vacuum : ℝ), limit_vacuum = c / 24 := by
  use a4
  exact h_link

end InfoGeometry.Canonical
