import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.Clifford.ManuscriptTheorems
import InfoGeometry.Canonical.DrazinPenroseAnomalyOwner
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.VarlamovDiscreteSymmetry

/-!
# Chiral-projector conservation under a declared Unruh flow

This file proves a conditional finite operator identity: if a supplied chiral
operator `Γ` commutes with the declared modular Hamiltonian, then the derived
projector commutes with `unruhFlow θ`.  It does not prove a Drazin anomaly
index theorem, Majorana zero-mode stability, or a `2e²/h` conductance result.
-/

open InfoGeometry.Dynamics
open InfoGeometry.Krein

namespace InfoGeometry.Dynamics.ThermalChiralConservation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
**The Chiral Pseudoscalar.** Γ in Cl(p,q) commutes with all even-graded elements.
-/
structure ChiralPseudoscalar (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  Gamma : DoubledSpace E →L[ℝ] DoubledSpace E
  Gamma_sq : Gamma.comp Gamma = ContinuousLinearMap.id ℝ (DoubledSpace E)
  /- Γ commutes with even-grade elements: B (boost), J (complex structure) -/
  commutes_with_modular : Gamma.comp (modularHamiltonian (E := E))
                      = (modularHamiltonian (E := E)).comp Gamma

variable (Chi : ChiralPseudoscalar E)

/--
Left chiral projector: P_+ = (1 + Γ)/2.
-/
noncomputable def chiral_proj_plus : EndH :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ H₂ + Chi.Gamma)

/--
Right chiral projector: P_- = (1 - Γ)/2.
-/
noncomputable def chiral_proj_minus : EndH :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ H₂ - Chi.Gamma)

/--
The declared Unruh flow commutes with the chiral projector `P_+`, using only
the supplied commutation of `Γ` with the modular Hamiltonian.
-/
theorem thermal_chiral_conservation (θ : ℝ) :
    (chiral_proj_plus Chi).comp (unruhFlow (E := E) θ) =
    (unruhFlow (E := E) θ).comp (chiral_proj_plus Chi) := by
  have hGammaFlow :
      Chi.Gamma.comp (unruhFlow (E := E) θ) =
        (unruhFlow (E := E) θ).comp Chi.Gamma := by
    simp [unruhFlow, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.smul_comp, Chi.commutes_with_modular]
  rw [chiral_proj_plus, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  congr 1
  rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hGammaFlow]
  simp

/--
Open owner obligation: connect the projector-conservation identity above to any
Drazin anomaly or conductance readout using a separate index and observable
model.
-/
/- The projector-conservation theorem and the transport observable have
   separate owners.  This export keeps the required Drazin/index data explicit
   rather than claiming that conservation alone implies conductance. -/
theorem drazin_anomaly_conductance_obligation
    {Op : InfoGeometry.Canonical.DrazinAnomaly.SpinorOp} {k : ℕ}
    (R : InfoGeometry.Canonical.TransportObservable.AndreevDrazinReadout Op k)
    (e_charge planck_h : ℝ) :
    R.zero_bias_conductance e_charge planck_h =
      InfoGeometry.Canonical.TransportObservable.conductance_quantum
        e_charge planck_h *
          |(InfoGeometry.Canonical.DrazinAnomaly.drazin_anomaly_index
            R.anomaly : ℝ)| :=
  R.majorana_conductance_peak e_charge planck_h

end InfoGeometry.Dynamics.ThermalChiralConservation
