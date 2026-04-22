import InfoGeometry.Canonical.WeylAnomalySource
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.ConformalAnomalyReadout
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic.NoncommRing

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.WeylKKTAnomalyIdentity

Thin closure layer that exposes the already-owned identities across:

- the operator algebra split (`commutator` / Jordan-anticommutator),
- the KKT/Weyl dilation source relation,
- and the anomaly-to-transported-Einstein residual route.

This file is intentionally compositional: it does not introduce a new anomaly
owner, a new dilation owner, or a new Einstein source model.
-/

namespace InfoGeometry.Canonical.WeylKKTAnomalyIdentity

open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.WeylInformationGauge
open InfoGeometry.Canonical.RicciMongeAmpere
section OperatorAlgebraClosure

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH₂" => H₂ →L[ℝ] H₂

/--
Symmetric anticommutator channel on the doubled carrier.
-/
@[rep_depth transport]
noncomputable def antiCommutator (A B : EndH₂) : EndH₂ :=
  (2 : ℝ)⁻¹ • (A * B + B * A)

/--
Clifford decomposition in KKT commutator form:
`AB = {A,B} + (1/2)[A,B]`.
-/
@[rep_depth transport]
theorem clifford_decomposition_kkt_form (A B : EndH₂) :
    A * B
      = antiCommutator A B
          + (2 : ℝ)⁻¹ • InfoGeometry.Canonical.KKTCore.commutator A B := by
  have hsum :
      (A * B + B * A) + (A * B - B * A) = (2 : ℝ) • (A * B) := by
    calc
      (A * B + B * A) + (A * B - B * A)
          = A * B + A * B := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm]
      _ = (2 : ℝ) • (A * B) := by
            simpa using (two_smul ℝ (A * B)).symm
  symm
  calc
    antiCommutator A B + (2 : ℝ)⁻¹ • InfoGeometry.Canonical.KKTCore.commutator A B
        = (2 : ℝ)⁻¹ • ((A * B + B * A) + (A * B - B * A)) := by
            simp [antiCommutator, InfoGeometry.Canonical.KKTCore.commutator, smul_add,
              sub_eq_add_neg]
    _ = (2 : ℝ)⁻¹ • ((2 : ℝ) • (A * B)) := by rw [hsum]
    _ = A * B := by simp [smul_smul]

end OperatorAlgebraClosure

section WeylAnomalyClosure

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ConformalInference

variable (CI : ConformalInference E)

/-- Scalar readout aliases are identical on the conformal anomaly lane. -/
@[rep_depth transport, simp]
theorem chiralScale_eq_epsilon :
    CI.chiralScale = CI.epsilon := by
  calc
    CI.chiralScale = CI.obstructionScale := CI.chiralScale_eq_obstructionScale
    _ = CI.epsilon := CI.epsilon_eq_obstructionScale.symm

/-- The `epsilon` readout is the norm of the projector-obstruction operator. -/
@[rep_depth transport, simp]
theorem epsilon_eq_projectorObstruction_nnnorm :
    CI.epsilon = ‖CI.projectorObstruction‖₊ := by
  calc
    CI.epsilon = CI.obstructionScale := CI.epsilon_eq_obstructionScale
    _ = ‖CI.projectorObstruction‖₊ := CI.obstructionScale_eq_projectorObstruction_nnnorm

/--
Structured dilation-source closure:
the Weyl dilation commutator is exactly `-1/2` times the obstruction operator.
-/
@[rep_depth transport]
theorem dilationCommutator_eq_neg_half_projectorObstruction_of_structuredProjectorHypotheses
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D
      = -((2 : ℝ)⁻¹) • CI.projectorObstruction := by
  exact
    CI.dilationSource_eq_neg_half_projectorObstruction_of_structuredProjectorHypotheses
      hProj hLeft

/--
Semantic-collapse packet for the operatorial Weyl anomaly lane:

- `chiralScale` and `epsilon` are the same scalar readout;
- both are the norm of the projector obstruction;
- the Weyl dilation commutator is sourced by that obstruction.
-/
@[rep_depth transport]
theorem semanticCollapsePacket
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.chiralScale = CI.epsilon
      ∧ CI.epsilon = ‖CI.projectorObstruction‖₊
      ∧ CI.P_D * CI.D - CI.D * CI.P_D
          = -((2 : ℝ)⁻¹) • CI.projectorObstruction := by
  refine ⟨chiralScale_eq_epsilon (CI := CI),
    epsilon_eq_projectorObstruction_nnnorm (CI := CI), ?_⟩
  exact
    dilationCommutator_eq_neg_half_projectorObstruction_of_structuredProjectorHypotheses
      (CI := CI) hProj hLeft

/--
Zero chiral scale collapses both projector obstruction and the Weyl dilation
commutator under the structured projector hypotheses.
-/
@[rep_depth transport]
theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_structuredProjectorHypotheses_of_chiralScale_eq_zero
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D)
    (hScaleZero : CI.chiralScale = 0) :
    CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  have hComm : Commute CI.spectralChiralProjector CI.metricChiralProjector := by
    simpa [Commute] using CI.projectors_commute_of_chiralScale_eq_zero hScaleZero
  have hObsZero : CI.projectorObstruction = 0 :=
    CI.projectorObstruction_eq_zero_of_commute hComm
  have hRight : CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D := by
    rw [hProj]
    exact hLeft
  have hDilZero : CI.P_D * CI.D - CI.D * CI.P_D = 0 :=
    CI.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero
      hRight hScaleZero
  exact ⟨hObsZero, hDilZero⟩

/--
Zero-scale semantic collapse packet: the scalar anomaly readouts vanish
together with projector obstruction and the Weyl dilation commutator.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_structuredProjectorHypotheses_of_chiralScale_eq_zero
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D)
    (hScaleZero : CI.chiralScale = 0) :
    CI.chiralScale = 0
      ∧ CI.epsilon = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  have hObsDil :=
    projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_structuredProjectorHypotheses_of_chiralScale_eq_zero
      (CI := CI) hProj hLeft hScaleZero
  have hEpsZero : CI.epsilon = 0 := by
    calc
      CI.epsilon = CI.chiralScale := by symm; exact chiralScale_eq_epsilon (CI := CI)
      _ = 0 := hScaleZero
  exact ⟨hScaleZero, hEpsZero, hObsDil.1, hObsDil.2⟩

end ConformalInference

end WeylAnomalyClosure

section EinsteinResidualClosure

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Operator-first Einstein source closure:
nonzero projector obstruction (`χ ≠ 0`) forces nonzero transported Einstein
residual under the standard source equation.
-/
@[rep_depth transport]
theorem nonzeroProjectorObstruction_sources_transportedEinsteinResidual
    (CBA : InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra E)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E)
    (x : E) (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hSource :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale)
    (hObs : CBA.CI.projectorObstruction ≠ 0) :
    transportedEinsteinResidual (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
  exact
    nonzeroAnomaly_sources_transportedEinsteinResidual
      (CI := CBA.CI) (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) (V := V) (Γ := Γ)
      hSource
      (by simpa [ConformalInference.projectorObstruction] using hObs)

end EinsteinResidualClosure

end InfoGeometry.Canonical.WeylKKTAnomalyIdentity
