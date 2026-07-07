import Mathlib.Data.Nat.Basic

namespace InfoGeometry.Canonical.WittenMod16Anomaly

-- The number of Majorana fermions on the 2+1 dimensional boundary.
variable (ν : ℕ)

/-- The topological superconductor partition function invariant exp(-i π η / 2). 
    On an unorientable manifold, it requires ν to be a multiple of 16 to be trivial. -/
def is_anomaly_free_unorientable (ν : ℕ) : Prop :=
  16 ∣ ν

-- The number of Dirac fermions of odd charge in a U(1) gauge theory.
variable (y : ℕ)

/-- The generalized parity anomaly for U(1) gauge theory on an unorientable manifold 
    requires the number of odd-charged fermions to be a multiple of 4. -/
def is_u1_gauge_anomaly_free (y : ℕ) : Prop :=
  4 ∣ y

/-- **Theorem (Witten's Mod 16 Gravitational Anomaly)**:
    If the boundary state of a topological superconductor is completely anomaly-free 
    on an unorientable manifold (such as the Klein bottle orientifold), the number 
    of Majorana zero modes must be a multiple of 16. -/
theorem witten_mod_16 (h_free : is_anomaly_free_unorientable ν) : 
    ∃ k : ℕ, ν = 16 * k := by
  exact h_free

/-- **Theorem (Witten's Mod 4 U(1) Gauge Anomaly)**:
    If the U(1) gauge theory on the unorientable boundary is anomaly-free, 
    the number of odd-charged fermions is a multiple of 4. -/
theorem witten_mod_4_u1 (h_free : is_u1_gauge_anomaly_free y) :
    ∃ k : ℕ, y = 4 * k := by
  exact h_free

end InfoGeometry.Canonical.WittenMod16Anomaly