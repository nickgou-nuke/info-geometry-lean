import InfoGeometry.Canonical.SpacetimeSynthesis

open CategoryTheory Limits

namespace InfoGeometry.Canonical

variable (Q : ∀ n, QuadraticForm ℝ (InfoGeometry.Topology.V n))
variable (h_compat : ∀ (m n : ℕ) (_h : m ≤ n) (x : InfoGeometry.Topology.V m),
  Q n (fun i => if h_lim : i.val < 2 * m then x ⟨i.val, h_lim⟩ else 0) = Q m x)
variable [HasColimit (CliffordTowerCausalFunctor Q h_compat)]

/--
  The unit group of the supplied Clifford-colimit vacuum carrier.  This is a
  finite algebraic gauge-symmetry proxy, not a Standard Model gauge-group
  theorem.
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
  If an observable `x` commutes with the unit `U`, conjugation by `U` fixes
  `x`.  This is the ordinary algebraic conjugation readout, not a Standard
  Model bosonic-symmetry theorem.
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
