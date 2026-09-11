import InfoGeometry.Physics.LorentzBoostKreinConfinement

/-!
# Axiom Audit: Lorentz Boost Generator and Krein Space Confinement

Verifies that the Lorentz boost generator, Krein space PT symmetry, and broken
PT symmetry charge collapse theorems rely strictly on standard Lean 4 foundations:
`propext`, `Classical.choice`, and `Quot.sound`.
-/

namespace InfoGeometry.Physics.LorentzBoostKreinConfinement.Audit

open InfoGeometry.Physics.LorentzBoostKreinConfinement

variable {H_space : Type*} [NormedAddCommGroup H_space] [InnerProductSpace ℝ H_space]
variable (K : KreinSpace H_space)

#print axioms broken_pt_symmetry_pair
#print axioms krein_null_charge_of_broken_pt
#print axioms unbroken_pt_of_nonzero_charge
#print axioms lorentz_boost_krein_confinement_synthesis

theorem lorentz_boost_krein_audit_soundness
    (A : H_space →ₗ[ℝ] H_space) (h_adjoint : IsKreinSelfAdjoint K A)
    (v : H_space) (lam1 lam2 : ℝ)
    (h_eigen1 : A v = lam1 • v) (h_eigen2 : K.J (A v) = lam2 • K.J v) :
    (lam1 ≠ lam2 → kreinCharge K v = 0) ∧
    (kreinCharge K v ≠ 0 → lam1 = lam2) ∧
    (K.J.comp K.J = LinearMap.id) :=
  lorentz_boost_krein_confinement_synthesis K A h_adjoint v lam1 lam2 h_eigen1 h_eigen2

#print axioms lorentz_boost_krein_audit_soundness

end InfoGeometry.Physics.LorentzBoostKreinConfinement.Audit
