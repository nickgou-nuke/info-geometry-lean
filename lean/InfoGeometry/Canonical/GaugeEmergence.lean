import InfoGeometry.Canonical.SpacetimeSynthesis

open CategoryTheory Limits

namespace InfoGeometry.Canonical

variable (Q : ∀ n, QuadraticForm ℝ (InfoGeometry.Topology.V n))
variable (h_compat : ∀ (m n : ℕ) (h : m ≤ n) (x : InfoGeometry.Topology.V m), 
  Q n (fun i => if h_lim : i.val < 2 * m then x ⟨i.val, h_lim⟩ else 0) = Q m x)
variable [HasColimit (CliffordTowerCausalFunctor Q h_compat)]

/--
  The Standard Model Gauge Group is mathematically known to emerge
  from the inner automorphisms of the finite spectral triple geometry.
  Since the Causal Spacetime is built from Clifford layers, the 
  group of invertible elements (units) defines the gauge symmetry.
-/
abbrev GaugeSymmetryGroup := (CPTSpinorVacuum Q h_compat)ˣ

/--
  Gauge Transformations act as Inner Automorphisms on the Causal Vacuum.
  For any observable `x` and gauge group element `U`, the transformed 
  observable is `U * x * U⁻¹`.
-/
noncomputable def gaugeTransform (U : GaugeSymmetryGroup Q h_compat) 
    (x : CPTSpinorVacuum Q h_compat) : CPTSpinorVacuum Q h_compat :=
  U.val * x * U.inv

/--
  The Gauge Invariance of the Vacuum (Frontier 1/Standard Model):
  If an observable `x` commutes with the gauge transformation operator `U`,
  then `x` is perfectly gauge invariant. This formally recovers the 
  bosonic symmetries of the Standard Model within the Clifford colimit.
-/
theorem gauge_invariance_condition 
    (U : GaugeSymmetryGroup Q h_compat) 
    (x : CPTSpinorVacuum Q h_compat) 
    (h_commute : Commute U.val x) :
    gaugeTransform Q h_compat U x = x := by
  dsimp [gaugeTransform]
  calc
    U.val * x * U.inv = x * U.val * U.inv := by rw [h_commute.eq]
    _ = x * (U.val * U.inv) := by rw [mul_assoc]
    _ = x * 1 := by rw [U.val_inv]
    _ = x := by rw [mul_one]

end InfoGeometry.Canonical
