import InfoGeometry.Physics.DilatonWeylAnomalyInflowBridge

/-!
# Axiom Audit: Dilaton Weyl Field, Callan-Harvey Anomaly Inflow, and Selberg Trace Bridge

Verifies that the dilaton flow, Weyl metric rescaling, Callan-Harvey anomaly inflow,
PT breaking charge collapse, and Selberg hyperbolic weight rely strictly on standard
foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`.
-/

namespace InfoGeometry.Physics.DilatonWeylAnomalyInflow.Audit

open InfoGeometry.Physics.DilatonWeylAnomalyInflow
open InfoGeometry.Physics.LorentzBoostKreinConfinement

variable {H_space : Type*} [NormedAddCommGroup H_space] [InnerProductSpace ℝ H_space]

#print axioms dilaton_flow_additive
#print axioms weylDilatonMetric_shift
#print axioms anomaly_inflow_conservation
#print axioms broken_pt_charge_collapse
#print axioms selberg_hyperbolic_weight_pos
#print axioms certified_dilaton_weyl_anomaly_synthesis

theorem dilaton_weyl_anomaly_audit_soundness
    (CH : CallanHarveyInflow H_space) (x t ell : ℝ) (hx : 0 < x) (h_ell : 0 < ell)
    (A : H_space →ₗ[ℝ] H_space) (h_adjoint : IsKreinSelfAdjoint CH.K A)
    (v : H_space) (lam1 lam2 : ℝ) (h_diff : lam1 ≠ lam2)
    (h_eigen1 : A v = lam1 • v) (h_eigen2 : CH.K.J (A v) = lam2 • CH.K.J v) :
    (dilatonField (dilationFlow t x) = dilatonField x + t) ∧
    (CH.bulkInflowCurrent = CH.seamAnomalyCurrent) ∧
    (seamNoetherCharge CH v = 0) ∧
    (0 < selbergHyperbolicWeight ell) :=
  certified_dilaton_weyl_anomaly_synthesis CH x t ell hx h_ell A h_adjoint v lam1 lam2 h_diff h_eigen1 h_eigen2

#print axioms dilaton_weyl_anomaly_audit_soundness

end InfoGeometry.Physics.DilatonWeylAnomalyInflow.Audit
