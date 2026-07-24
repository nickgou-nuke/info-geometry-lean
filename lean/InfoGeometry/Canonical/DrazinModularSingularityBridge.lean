import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.Cl11LorentzAction
import InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.DrazinModularSingularityBridge

Operatorial bridge translating "apex singularity" language into:

- defect/support projection obstruction,
- canonical defect-supported central channel,
- canonical kinetic remainder,
- modular-flow fixedness under explicit commutation hypotheses.
-/

namespace InfoGeometry.Canonical.DrazinModularSingularityBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Defect-projection commutator obstruction on the Drazin lane. -/
@[rep_depth operator]
noncomputable def defectProjectionObstruction
    (CIK : CertifiedInverseKernel H₂)
    (Y : EndH) : EndH :=
  DrazinSupercharge.commutator CIK.spectralComplementaryProjector Y

/-- Vanishing obstruction is exactly commutation with the defect projector. -/
@[rep_depth operator]
theorem defectProjectionObstruction_eq_zero_iff_commute
    (CIK : CertifiedInverseKernel H₂)
    (Y : EndH) :
    defectProjectionObstruction (CIK := CIK) Y = 0
      ↔ Commute CIK.spectralComplementaryProjector Y := by
  unfold defectProjectionObstruction DrazinSupercharge.commutator
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h.eq

/--
Canonical singular channel package:
`Z_D` is defect-supported and Drazin-lane central.
-/
@[rep_depth operator]
theorem canonicalDefectCentral_singularity_package
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.IsDefectSupported CIK
        (DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral CIK)
      ∧
    DrazinSupercharge.CertifiedInverseKernel.IsDrazinLaneCentral CIK
        (DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral CIK) := by
  exact ⟨
    DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral_isDefectSupported
      (CIK := CIK),
    DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentral_isDrazinLaneCentral
      (CIK := CIK)
  ⟩

/--
Canonical kinetic channel package:
`H_K` has vanishing defect block.
-/
@[rep_depth operator]
theorem canonicalKineticPart_singularity_package
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.HasVanishingDefectBlock CIK
      (DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPart (CIK := CIK)) := by
  exact
    DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPart_hasVanishingDefectBlock
      (CIK := CIK)

/--
Functional-calculus seal on the Drazin regular lane.

This package exposes, in the singularity bridge itself, the certified passage:
`Δ|Preg -> log -> Kreg -> Kambient`, together with defect-lane exclusion.
-/
@[rep_depth transport, capstone]
theorem drazin_regular_functionalCalculus_seal
    (c : CertifiedModularReduction (E := H₂)) :
    let KambientCanonical :=
      compress (CertifiedModularReduction.Preg c)
        (K_neg_log_PregDelta (V := E) c)
    c.logAdmissible (compress (CertifiedModularReduction.Preg c) c.Δ)
      ∧ ¬ c.logAdmissible (compress (CertifiedModularReduction.Pzero c) c.Δ)
      ∧ (CertifiedModularReduction.Preg c * KambientCanonical = KambientCanonical)
      ∧ (KambientCanonical * CertifiedModularReduction.Preg c = KambientCanonical)
      ∧ (CertifiedModularReduction.Pzero c * KambientCanonical = 0)
      ∧ (KambientCanonical * CertifiedModularReduction.Pzero c = 0) := by
  intro KambientCanonical
  have hLog :
      c.logAdmissible
        (compress (CertifiedModularReduction.Preg c) c.Δ) :=
    log_defined_on_Preg (V := E) c
  have hNoLog :
      ¬ c.logAdmissible
        (compress (CertifiedModularReduction.Pzero c) c.Δ) :=
    canonicalTomita_no_log_on_Pzero_of_certifiedReduction (V := E) c
  have hSupportPkg :
      (CertifiedModularReduction.Preg c * KambientCanonical = KambientCanonical)
        ∧ (KambientCanonical * CertifiedModularReduction.Preg c = KambientCanonical)
        ∧ (CertifiedModularReduction.Pzero c * KambientCanonical = 0)
        ∧ (KambientCanonical * CertifiedModularReduction.Pzero c = 0) := by
    simpa [KambientCanonical] using
      (K_neg_log_PregDelta_support_package (V := E) c)
  exact ⟨hLog, hNoLog, hSupportPkg.1, hSupportPkg.2.1, hSupportPkg.2.2.1, hSupportPkg.2.2.2⟩

/--
Operator-ratio regularization corridor.

The finite RedLine owner represents the relative modular operator as the
projective ratio `dμ / dν` and reads its modular Hamiltonian as
`-log(dμ / dν)`. In the singular operator lane this global ratio must not be
formed across the defect kernel. The certified Drazin/Penrose package instead
separates:

- `Preg`: the Drazin regular support on which the logarithm is certified;
- `Pzero`: the Drazin defect/null lane on which no logarithm certificate exists;
- `Pmetric`: the Moore-Penrose metric lane used for physical compression.

This theorem is the named algebraic seal for that corridor. It exposes only the
proved facts: regular-lane log admissibility, defect-lane exclusion, support of
the canonical generator on `Preg`, annihilation of `Pzero`, and the Penrose
alignment criterion for the remaining metric compression.
-/
@[rep_depth transport, capstone]
theorem operator_ratio_regularization_corridor
    (c : CertifiedModularReduction (E := H₂)) :
    let KambientCanonical :=
      compress (CertifiedModularReduction.Preg c)
        (K_neg_log_PregDelta (V := E) c)
    c.logAdmissible (CertifiedModularReduction.Δreg c)
      ∧ ¬ c.logAdmissible (compress (CertifiedModularReduction.Pzero c) c.Δ)
      ∧ (CertifiedModularReduction.Preg c * KambientCanonical = KambientCanonical)
      ∧ (KambientCanonical * CertifiedModularReduction.Preg c = KambientCanonical)
      ∧ (CertifiedModularReduction.Pzero c * KambientCanonical = 0)
      ∧ (KambientCanonical * CertifiedModularReduction.Pzero c = 0)
      ∧ (CertifiedModularReduction.anomaly c = 0
          ↔ CertifiedModularReduction.SpectralMetricAlignment c) := by
  intro KambientCanonical
  have hSeal := drazin_regular_functionalCalculus_seal (E := E) c
  have hAlign := CertifiedModularReduction.anomaly_vanishes_iff_alignment (c := c)
  exact ⟨
    by simpa [CertifiedModularReduction.Δreg] using hSeal.1,
    hSeal.2.1,
    hSeal.2.2.1,
    hSeal.2.2.2.1,
    hSeal.2.2.2.2.1,
    hSeal.2.2.2.2.2,
    hAlign
  ⟩

@[rep_depth transport, capstone]
theorem certified_operator_ratio_regularization_corridor
    (c : CertifiedModularReduction (E := H₂)) :
    let KambientCanonical :=
      compress (CertifiedModularReduction.Preg c)
        (K_neg_log_PregDelta (V := E) c)
    c.logAdmissible (CertifiedModularReduction.Δreg c)
      ∧ ¬ c.logAdmissible (compress (CertifiedModularReduction.Pzero c) c.Δ)
      ∧ (CertifiedModularReduction.Preg c * KambientCanonical = KambientCanonical)
      ∧ (KambientCanonical * CertifiedModularReduction.Preg c = KambientCanonical)
      ∧ (CertifiedModularReduction.Pzero c * KambientCanonical = 0)
      ∧ (KambientCanonical * CertifiedModularReduction.Pzero c = 0)
      ∧ (CertifiedModularReduction.anomaly c = 0
          ↔ CertifiedModularReduction.SpectralMetricAlignment c) :=
  operator_ratio_regularization_corridor (E := E) c

/--
Noncommutative regularized-ratio closure under spectral/metric alignment.

This is the next proved step after the regularization corridor: once the
Drazin-regular logarithm has been formed on `Preg` and the Penrose metric lane
is aligned with the Drazin support, the physical generator `Kphys` has no
leakage through the defect/null projector `Pzero`.

No finite diagonal model is used here. The proof runs only through the certified
regular-lane operator package and the Drazin/Penrose projector algebra.
-/
@[rep_depth transport, capstone]
theorem operator_ratio_regularization_kills_defect_of_alignment
    (c : CertifiedModularReduction (E := H₂))
    (hAlign : CertifiedModularReduction.SpectralMetricAlignment (c := c)) :
    c.logAdmissible (CertifiedModularReduction.Δreg c)
      ∧ (CertifiedModularReduction.Pzero c * CertifiedModularReduction.Kphys c = 0)
      ∧ (CertifiedModularReduction.Kphys c * CertifiedModularReduction.Pzero c = 0) := by
  have hCorridor := operator_ratio_regularization_corridor (E := E) c
  have hAnomaly :
      CertifiedModularReduction.anomaly c = 0 :=
    hCorridor.2.2.2.2.2.2.mpr hAlign
  have hKill :=
    CertifiedModularReduction.Kphys_kills_Pzero_of_alignment (c := c) hAnomaly
  exact ⟨hCorridor.1, hKill.1, hKill.2⟩

@[rep_depth transport, capstone]
theorem certified_operator_ratio_regularization_kills_defect_of_alignment
    (c : CertifiedModularReduction (E := H₂))
    (hAlign : CertifiedModularReduction.SpectralMetricAlignment (c := c)) :
    c.logAdmissible (CertifiedModularReduction.Δreg c)
      ∧ (CertifiedModularReduction.Pzero c * CertifiedModularReduction.Kphys c = 0)
      ∧ (CertifiedModularReduction.Kphys c * CertifiedModularReduction.Pzero c = 0) :=
  operator_ratio_regularization_kills_defect_of_alignment (E := E) c hAlign

/--
Noncommutative regularized-ratio closure under the inertial-lane formulation.

This is the same theorem with the existing `InertialRegularLane` predicate
(`anomaly = 0`) as input.
-/
@[rep_depth transport, capstone]
theorem operator_ratio_regularization_kills_defect_of_inertial_lane
    (c : CertifiedModularReduction (E := H₂))
    (hInertial : CertifiedModularReduction.InertialRegularLane (c := c)) :
    c.logAdmissible (CertifiedModularReduction.Δreg c)
      ∧ (CertifiedModularReduction.Pzero c * CertifiedModularReduction.Kphys c = 0)
      ∧ (CertifiedModularReduction.Kphys c * CertifiedModularReduction.Pzero c = 0) := by
  have hAlign :
      CertifiedModularReduction.SpectralMetricAlignment (c := c) :=
    (CertifiedModularReduction.inertial_regular_lane_iff_alignment (c := c)).mp hInertial
  exact operator_ratio_regularization_kills_defect_of_alignment
    (E := E) c hAlign

@[rep_depth transport, capstone]
theorem certified_operator_ratio_regularization_kills_defect_of_inertial_lane
    (c : CertifiedModularReduction (E := H₂))
    (hInertial : CertifiedModularReduction.InertialRegularLane (c := c)) :
    c.logAdmissible (CertifiedModularReduction.Δreg c)
      ∧ (CertifiedModularReduction.Pzero c * CertifiedModularReduction.Kphys c = 0)
      ∧ (CertifiedModularReduction.Kphys c * CertifiedModularReduction.Pzero c = 0) :=
  operator_ratio_regularization_kills_defect_of_inertial_lane (E := E) c hInertial

/--
Inertial regular-lane closure package (`χ = 0`):

- regular-lane logarithm is admitted on `Preg Δ`,
- the physical compressed generator has no defect leakage across `Pzero`.
-/
@[rep_depth operator]
theorem inertial_regular_lane_closure_package
    (c : CertifiedModularReduction (E := H₂))
    (hInertial : CertifiedModularReduction.InertialRegularLane (c := c)) :
    c.logAdmissible (compress (CertifiedModularReduction.Preg c) c.Δ)
      ∧ (CertifiedModularReduction.Pzero c * CertifiedModularReduction.Kphys c = 0)
      ∧ (CertifiedModularReduction.Kphys c * CertifiedModularReduction.Pzero c = 0) := by
  have hLog :
      c.logAdmissible (compress (CertifiedModularReduction.Preg c) c.Δ) :=
    log_defined_on_Preg (V := E) c
  have hKill :
      CertifiedModularReduction.Pzero c * CertifiedModularReduction.Kphys c = 0
        ∧
      CertifiedModularReduction.Kphys c * CertifiedModularReduction.Pzero c = 0 :=
    CertifiedModularReduction.Kphys_kills_Pzero_of_inertial_regular_lane
      (c := c) hInertial
  exact ⟨hLog, hKill.1, hKill.2⟩

/--
Curved regular lane (`χ ≠ 0`) is exactly the alignment obstruction.
-/
@[rep_depth operator]
theorem curved_regular_lane_obstructs_alignment
    (c : CertifiedModularReduction (E := H₂))
    (hCurved : CertifiedModularReduction.CurvedRegularLane (c := c)) :
    ¬ CertifiedModularReduction.SpectralMetricAlignment (c := c) :=
  (CertifiedModularReduction.curved_regular_lane_iff_non_alignment (c := c)).1 hCurved

/-- Modular adjoint transport of an operator along the true modular flow. -/
@[rep_depth transport]
noncomputable def modularAdjointFlow
    (hMod : EndH) (t : ℝ) (A : EndH) : EndH :=
  modularTransportFlow (E := E) hMod t * A * modularTransportFlow (E := E) hMod (-t)

/-- The modular adjoint flow is identity at `t = 0`. -/
@[rep_depth transport]
theorem modularAdjointFlow_zero
    (hMod : EndH) (A : EndH) :
    modularAdjointFlow hMod 0 A = A := by
  let _ : CompleteSpace E := inferInstance
  unfold modularAdjointFlow
  simp

/--
If `A` commutes pointwise with the modular transport flow, it is fixed under
modular adjoint transport.
-/
@[rep_depth transport]
theorem modularAdjointFlow_eq_self_of_commute_flow
    (hMod : EndH) (A : EndH) (t : ℝ)
    (hComm : ∀ τ : ℝ, Commute A (modularTransportFlow (E := E) hMod τ)) :
    modularAdjointFlow hMod t A = A := by
  set U : ℝ → EndH := modularTransportFlow (E := E) hMod
  have hCommT : U t * A = A * U t := by
    simpa [U] using (hComm t).eq.symm
  unfold modularAdjointFlow
  calc
    U t * A * U (-t) = (A * U t) * U (-t) := by rw [hCommT]
    _ = A * (U t * U (-t)) := by simp [mul_assoc]
    _ = A * U (t + (-t)) := by
          rw [← modularTransportFlow_add (E := E) hMod t (-t)]
    _ = A * U 0 := by simp
    _ = A * 1 := by
          have hU0 : U 0 = 1 := by
            change modularTransportFlow (E := E) hMod 0 = 1
            exact modularTransportFlow_zero (E := E) hMod
          simp [hU0]
    _ = A := by simp

/--
If `A` commutes with the modular transport generator, it is fixed under
modular adjoint transport.
-/
@[rep_depth transport]
theorem modularAdjointFlow_eq_self_of_commute_generator
    (hMod : EndH) (A : EndH) (t : ℝ)
    (hCommGen : Commute A (modularTransportGenerator (E := E) hMod)) :
    modularAdjointFlow hMod t A = A := by
  have hCommFlow : ∀ τ : ℝ, Commute A (modularTransportFlow (E := E) hMod τ) := by
    intro τ
    simpa [modularTransportFlow] using ((hCommGen.smul_right τ).exp_right)
  exact modularAdjointFlow_eq_self_of_commute_flow (E := E) hMod A t hCommFlow

/--
Interoperability bridge: if the transport flow in this lane is identified with
the `Cl11LorentzAction.modularFlow`, then both adjoint surfaces coincide.
-/
@[rep_depth transport]
theorem modularAdjointFlow_eq_cl11_modularAdjointFlow_of_flow_eq
    (X : InfoGeometry.Quantum.RealSplitCl11Action (DoubledSpace E))
    (hMod : EndH) (t : ℝ) (A : EndH)
    (hFlowEq : ∀ τ : ℝ,
      modularTransportFlow (E := E) hMod τ
        = InfoGeometry.Canonical.Cl11LorentzAction.modularFlow
            (H := DoubledSpace E) X τ) :
    modularAdjointFlow (E := E) hMod t A
      = InfoGeometry.Canonical.Cl11LorentzAction.modularAdjointFlow
          (H := DoubledSpace E) X t A := by
  unfold modularAdjointFlow InfoGeometry.Canonical.Cl11LorentzAction.modularAdjointFlow
  rw [hFlowEq t, hFlowEq (-t)]

/--
Modular fixedness bridge for the canonical defect-supported central channel.
-/
@[rep_depth transport]
theorem modularAdjointFlow_canonicalDefectCentral_eq_self_of_commute_generator
    (CIK : CertifiedInverseKernel H₂)
    (hMod : EndH) (t : ℝ)
    (hCommGen :
      Commute
        (DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK)
        (modularTransportGenerator (E := E) hMod)) :
    modularAdjointFlow hMod t
      (DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK)
      =
    DrazinSupercharge.CertifiedInverseKernel.canonicalDefectCentralK CIK := by
  exact modularAdjointFlow_eq_self_of_commute_generator (E := E) hMod _ t hCommGen

/--
Modular fixedness bridge for the canonical kinetic remainder.
-/
@[rep_depth transport]
theorem modularAdjointFlow_canonicalKineticPart_eq_self_of_commute_generator
    (CIK : CertifiedInverseKernel H₂)
    (hMod : EndH) (t : ℝ)
    (hCommGen :
      Commute
        (DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK (CIK := CIK))
        (modularTransportGenerator (E := E) hMod)) :
    modularAdjointFlow hMod t
      (DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK (CIK := CIK))
      =
    DrazinSupercharge.CertifiedInverseKernel.canonicalKineticPartK (CIK := CIK) := by
  exact modularAdjointFlow_eq_self_of_commute_generator (E := E) hMod _ t hCommGen

/--
Capstone API name: projected odd supercharge `Q_D` is preserved under modular
adjoint transport when it commutes with the modular generator.
-/
@[rep_depth transport]
theorem qD_preserved_under_modularFlow_of_commute_theta
    (CIK : CertifiedInverseKernel H₂)
    (θ : EndH) (t : ℝ)
    (hCommGen :
      Commute
        (DrazinSupercharge.CertifiedInverseKernel.superchargeK CIK)
        (modularTransportGenerator (E := E) θ)) :
    modularAdjointFlow θ t
      (DrazinSupercharge.CertifiedInverseKernel.superchargeK CIK)
      =
    DrazinSupercharge.CertifiedInverseKernel.superchargeK CIK := by
  exact modularAdjointFlow_eq_self_of_commute_generator (E := E) θ _ t hCommGen

/--
Capstone API name: projected even generator `H_D = Q_D^2` is fixed under
modular adjoint transport when it commutes with the modular generator.
-/
@[rep_depth transport]
theorem hD_fixed_under_modularFlow_of_commute_theta
    (CIK : CertifiedInverseKernel H₂)
    (θ : EndH) (t : ℝ)
    (hCommGen :
      Commute
        (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
        (modularTransportGenerator (E := E) θ)) :
    modularAdjointFlow θ t
      (DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK)
      =
    DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK CIK := by
  exact modularAdjointFlow_eq_self_of_commute_generator (E := E) θ _ t hCommGen

end Core

end InfoGeometry.Canonical.DrazinModularSingularityBridge
