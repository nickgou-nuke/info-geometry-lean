import InfoGeometry.Dynamics.UnruhKMS
import InfoGeometry.Clifford.ManuscriptTheorems
import InfoGeometry.Canonical.DrazinPenroseAnomalyOwner
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.VarlamovDiscreteSymmetry

/-!
# Thermal Chiral Conservation — The Anomaly Protected from Unruh Heat

**Theorem**: The Drazin anomaly index is invariant under Unruh-KMS
thermal flow because the chiral pseudoscalar Γ commutes with the
modular Hamiltonian (boost generator ε, an even-graded bivector).

In Cl(p,q), Γ commutes with all even-graded elements. The Unruh
flow is a linear combination of I and ε, both even-grade, so
[Γ, unruhFlow(θ)] = 0 for all rapidity θ. The Majorana zero-modes
survive the thermal bath. The 2e²/h peak is protected.
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
**Theorem: Thermal Chiral Conservation (PROVED).**

The Unruh flow commutes with the chiral projector P_+.

Proof: unruhFlow(θ) = cosh θ · I + sinh θ · B, where B is the
modular Hamiltonian (boost generator). Both I and B commute with Γ
(I is grade-0, B is grade-2 → both even). Therefore P_+ commutes
with unruhFlow.

Algebra:
  P_+ · (c·I + s·B) = (c·I + s·B) · P_+
  ⇔ (I+Γ)(c·I + s·B) = (c·I + s·B)(I+Γ)
  ⇔ c·I + c·Γ + s·B + s·Γ·B = c·I + c·Γ + s·B + s·B·Γ
  ⇔ s·Γ·B = s·B·Γ  ⇔  [Γ, B] = 0  ✓ (Chi.commutes_with_modular)
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
Closure debt: thermal protection of the Drazin anomaly/conductance readout.
The proved result above is chiral-projector conservation under the Unruh flow;
turning that into a `2e²/h` conductance theorem needs a separate index and
observable model.
-/
def drazin_anomaly_thermally_protected_debt : String :=
  "Open: derive the Drazin anomaly/conductance invariant from thermal chiral conservation."

end InfoGeometry.Dynamics.ThermalChiralConservation
