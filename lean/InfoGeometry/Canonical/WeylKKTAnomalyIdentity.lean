import InfoGeometry.Canonical.WeylAnomalySource
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.ConformalAnomalyReadout
import InfoGeometry.Canonical.SouriauPlanckVector
import InfoGeometry.Canonical.IncompressibleBitBridge
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
Proof-carrying witness for the structured projector hypotheses on the Weyl/KKT
anomaly lane.

This packages the paired projector identities into one constructive witness so
downstream collapse routes need not carry the raw `hProj`/`hLeft` pair.
-/
@[rep_depth transport]
abbrev StructuredProjectorHypothesesWitness : Prop :=
  CI.P_MP_right = CI.P_MP ∧ CI.P_D * CI.P_MP = CI.P_MP * CI.P_D

/--
Proof-carrying RN/Kähler witness for the conformal zero-scale lane.

This bundles the Kähler readback identification together with the owned
unit-relative-volume bit, so downstream zero-collapse routes need not carry the
raw `(hScaleFromKahler, bit)` pair.
-/
@[rep_depth transport]
abbrev UnitRelativeVolumeScaleWitness
    {n : Nat} (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n) : Prop :=
  CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M ∧
    InfoGeometry.Canonical.IncompressibleBitBridge.UnitRelativeVolumeBit n M

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
Witness-routed version of the structured dilation-source closure theorem.
-/
@[rep_depth transport]
theorem dilationCommutator_eq_neg_half_projectorObstruction_of_structuredProjectorWitness
    (W : StructuredProjectorHypothesesWitness (CI := CI)) :
    CI.P_D * CI.D - CI.D * CI.P_D
      = -((2 : ℝ)⁻¹) • CI.projectorObstruction := by
  exact
    dilationCommutator_eq_neg_half_projectorObstruction_of_structuredProjectorHypotheses
      (CI := CI) W.1 W.2

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

/--
Zero-scale semantic collapse packet through the proof-carrying structured
projector witness.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_structuredProjectorWitness_of_chiralScale_eq_zero
    (W : StructuredProjectorHypothesesWitness (CI := CI))
    (hScaleZero : CI.chiralScale = 0) :
    CI.chiralScale = 0
      ∧ CI.epsilon = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  have hObsDil :=
    projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_structuredProjectorHypotheses_of_chiralScale_eq_zero
      (CI := CI) W.1 W.2 hScaleZero
  have hEpsZero : CI.epsilon = 0 := by
    calc
      CI.epsilon = CI.chiralScale := by symm; exact chiralScale_eq_epsilon (CI := CI)
      _ = 0 := hScaleZero
  exact ⟨hScaleZero, hEpsZero, hObsDil.1, hObsDil.2⟩

/--
Smaller constructive projector/dilation zero packet from the proof-carrying
unit-relative-volume bit route.

This removes the explicit `hScaleZero : CI.chiralScale = 0` gate when the
caller already owns the RN/Kähler witness packet forcing zero chiral scale.
-/
@[rep_depth transport]
theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_unitRelativeVolumeBit_of_structuredProjectorHypotheses
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler :
      CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M)
    (bit : InfoGeometry.Canonical.IncompressibleBitBridge.UnitRelativeVolumeBit n M)
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  exact
    projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_structuredProjectorHypotheses_of_chiralScale_eq_zero
      (CI := CI) hProj hLeft
      (InfoGeometry.Canonical.IncompressibleBitBridge.chiralScale_eq_zero_of_unitRelativeVolumeBit
        (CI := CI) (M := M) hScaleFromKahler bit)

/--
Smaller constructive projector/dilation zero packet through the proof-carrying
structured projector witness and the unit-relative-volume bit route.

This removes the raw `hProj`/`hLeft` projector pair together with the explicit
`hScaleZero : CI.chiralScale = 0` gate when the caller already owns both
constructive witness packets.
-/
@[rep_depth transport]
theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_unitRelativeVolumeBit_of_structuredProjectorWitness
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler :
      CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M)
    (bit : InfoGeometry.Canonical.IncompressibleBitBridge.UnitRelativeVolumeBit n M)
    (W : StructuredProjectorHypothesesWitness (CI := CI)) :
    CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  exact
    projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_unitRelativeVolumeBit_of_structuredProjectorHypotheses
      (CI := CI) (M := M) hScaleFromKahler bit W.1 W.2

/--
Smaller constructive projector/dilation zero packet from a single RN/Kähler
witness packet together with the structured projector witness.

This removes the explicit `(hScaleFromKahler, bit)` pair from the theorem
surface when the caller already owns the proof-carrying
`UnitRelativeVolumeScaleWitness`.
-/
@[rep_depth transport]
theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_unitRelativeVolumeScaleWitness_of_structuredProjectorWitness
    {n : Nat}
    {M : InfoGeometry.Canonical.MoE.SinkhornMatrix n}
    (WV : UnitRelativeVolumeScaleWitness (CI := CI) M)
    (W : StructuredProjectorHypothesesWitness (CI := CI)) :
    CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  exact
    projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_unitRelativeVolumeBit_of_structuredProjectorWitness
      (CI := CI) (M := M) WV.1 WV.2 W

end ConformalInference

end WeylAnomalyClosure

section SouriauWeylClosure

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ConformalInference

variable (CI : ConformalInference E)

/--
Proof-carrying witness that thermodynamic readout stationarity forces vanishing
chiral scale for the current conformal inference packet.

This is the smallest honest constructive replacement for the bare bridge
hypothesis
`IsThermodynamicReadoutStationary ... → CI.chiralScale = 0`.
-/
@[rep_depth transport]
abbrev StationaryScaleZeroWitness
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : InfoGeometry.Krein.DoubledSpace E)
    (A : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) : Prop :=
  InfoGeometry.Canonical.ThermodynamicGenerator.IsThermodynamicReadoutStationary
      (E := E) P ψ A → CI.chiralScale = 0

/--
Recover the stationarity-to-zero-scale bridge from the proof-carrying witness.
-/
@[rep_depth transport]
theorem stationaryScaleZero_of_witness
    {P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)}
    {ψ : InfoGeometry.Krein.DoubledSpace E}
    {A : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E}
    (W : StationaryScaleZeroWitness (E := E) CI P ψ A) :
    InfoGeometry.Canonical.ThermodynamicGenerator.IsThermodynamicReadoutStationary
        (E := E) P ψ A → CI.chiralScale = 0 :=
  W

/--
Souriau-to-Weyl zero-scale packet through an explicit stationarity readout.

This theorem does not assert the false unconditional claim that a
`GibbsSouriauEquilibriumSeed` alone determines the conformal anomaly scale.
It removes the low-level `hScaleZero` gate only when the caller supplies the
missing semantic witness from thermodynamic readout stationarity to
`CI.chiralScale = 0`.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_equilibriumSeed_of_stationaryScaleZeroWitness_of_structuredProjectorHypotheses
    {P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)}
    {ψ : InfoGeometry.Krein.DoubledSpace E}
    {A : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E}
    (hEq :
      InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed
        (E := E) P ψ A)
    (W : StationaryScaleZeroWitness (E := E) CI P ψ A)
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.chiralScale = 0
      ∧ CI.epsilon = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  have hStationary :
      InfoGeometry.Canonical.ThermodynamicGenerator.IsThermodynamicReadoutStationary
        (E := E) P ψ A :=
    InfoGeometry.Canonical.SouriauPlanckVector.isThermodynamicReadoutStationary_of_equilibriumSeed
      (E := E) hEq
  exact
    semanticCollapsePacket_of_structuredProjectorHypotheses_of_chiralScale_eq_zero
      (CI := CI) hProj hLeft
      (stationaryScaleZero_of_witness (E := E) (CI := CI) W hStationary)

/--
Souriau-to-Weyl zero-scale packet through explicit stationarity and structured
projector witness packets.

This removes the raw `hProj`/`hLeft` pair from the equilibrium-seed route when
callers already own the proof-carrying projector witness.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_equilibriumSeed_of_stationaryScaleZeroWitness_of_structuredProjectorWitness
    {P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)}
    {ψ : InfoGeometry.Krein.DoubledSpace E}
    {A : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E}
    (hEq :
      InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed
        (E := E) P ψ A)
    (WScale : StationaryScaleZeroWitness (E := E) CI P ψ A)
    (WProj : StructuredProjectorHypothesesWitness (CI := CI)) :
    CI.chiralScale = 0
      ∧ CI.epsilon = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  exact
    semanticCollapsePacket_of_equilibriumSeed_of_stationaryScaleZeroWitness_of_structuredProjectorHypotheses
      (CI := CI) hEq WScale WProj.1 WProj.2

/--
Souriau-to-Weyl zero-scale packet through an explicit stationarity readout.

This theorem does not assert the false unconditional claim that a
`GibbsSouriauEquilibriumSeed` alone determines the conformal anomaly scale.
It removes the low-level `hScaleZero` gate only when the caller supplies the
missing semantic witness from thermodynamic readout stationarity to
`CI.chiralScale = 0`.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_equilibriumSeed_of_structuredProjectorHypotheses
    {P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)}
    {ψ : InfoGeometry.Krein.DoubledSpace E}
    {A : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E}
    (hEq :
      InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed
        (E := E) P ψ A)
    (hStationaryToScaleZero :
      InfoGeometry.Canonical.ThermodynamicGenerator.IsThermodynamicReadoutStationary
        (E := E) P ψ A → CI.chiralScale = 0)
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.chiralScale = 0
      ∧ CI.epsilon = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  exact
    semanticCollapsePacket_of_equilibriumSeed_of_stationaryScaleZeroWitness_of_structuredProjectorHypotheses
      (CI := CI) hEq hStationaryToScaleZero hProj hLeft


/--
Smaller constructive zero-scale packet from the proof-carrying unit-relative-volume
bit route.

This removes the explicit bridge hypothesis
`hStationaryToScaleZero : IsThermodynamicReadoutStationary ... → CI.chiralScale = 0`
when the caller already owns the RN/Kähler witness packet forcing
`CI.chiralScale = 0`.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_unitRelativeVolumeBit_of_structuredProjectorHypotheses
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler :
      CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M)
    (bit : InfoGeometry.Canonical.IncompressibleBitBridge.UnitRelativeVolumeBit n M)
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.chiralScale = 0
      ∧ CI.epsilon = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  exact
    semanticCollapsePacket_of_structuredProjectorHypotheses_of_chiralScale_eq_zero
      (CI := CI) hProj hLeft
      (InfoGeometry.Canonical.IncompressibleBitBridge.chiralScale_eq_zero_of_unitRelativeVolumeBit
        (CI := CI) (M := M) hScaleFromKahler bit)

/--
Smaller constructive zero-scale packet through the proof-carrying structured
projector witness and the unit-relative-volume bit route.

This removes the raw `hProj`/`hLeft` projector pair together with the explicit
bridge-to-zero-scale hypothesis when the caller already owns both constructive
witness packets.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_unitRelativeVolumeBit_of_structuredProjectorWitness
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler :
      CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M)
    (bit : InfoGeometry.Canonical.IncompressibleBitBridge.UnitRelativeVolumeBit n M)
    (W : StructuredProjectorHypothesesWitness (CI := CI)) :
    CI.chiralScale = 0
      ∧ CI.epsilon = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  exact
    semanticCollapsePacket_of_unitRelativeVolumeBit_of_structuredProjectorHypotheses
      (CI := CI) (M := M) hScaleFromKahler bit W.1 W.2

/--
Smaller constructive zero-scale packet from a single RN/Kähler witness packet
and the structured projector witness.

This removes the explicit `(hScaleFromKahler, bit)` pair from the theorem
surface when the caller already owns the proof-carrying
`UnitRelativeVolumeScaleWitness`.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_unitRelativeVolumeScaleWitness_of_structuredProjectorWitness
    {n : Nat}
    {M : InfoGeometry.Canonical.MoE.SinkhornMatrix n}
    (WV : UnitRelativeVolumeScaleWitness (CI := CI) M)
    (W : StructuredProjectorHypothesesWitness (CI := CI)) :
    CI.chiralScale = 0
      ∧ CI.epsilon = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  exact
    semanticCollapsePacket_of_unitRelativeVolumeBit_of_structuredProjectorWitness
      (CI := CI) (M := M) WV.1 WV.2 W

/--
Souriau-to-Weyl zero-scale packet from the smaller constructive thermodynamic
surface: faithful probing plus vanishing first variation.  This removes the
need to carry `GibbsSouriauEquilibriumSeed` as a bridge hypothesis when the raw
stationarity witness is already available.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_firstVariation_eq_zero_of_probeFaithful_of_stationaryScaleZeroWitness
    {P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)}
    {ψ : InfoGeometry.Krein.DoubledSpace E}
    {A : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E}
    (hFaithful : InfoGeometry.Canonical.ThermodynamicGenerator.ProbeFaithful (E := E) P)
    (hFirst :
      InfoGeometry.Canonical.RelativeModularPotential.firstVariation (E := E) P ψ A = 0)
    (W : StationaryScaleZeroWitness (E := E) CI P ψ A)
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.chiralScale = 0
      ∧ CI.epsilon = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  have hStationary :
      InfoGeometry.Canonical.ThermodynamicGenerator.IsThermodynamicReadoutStationary
        (E := E) P ψ A :=
    InfoGeometry.Canonical.SouriauPlanckVector.isThermodynamicReadoutStationary_of_firstVariation_eq_zero_of_probeFaithful
      (E := E) hFaithful hFirst
  exact
    semanticCollapsePacket_of_structuredProjectorHypotheses_of_chiralScale_eq_zero
      (CI := CI) hProj hLeft
      (stationaryScaleZero_of_witness (E := E) (CI := CI) W hStationary)

/--
Smaller constructive zero-scale packet from the proof-carrying stationarity to
scale-zero witness.  This removes the bare bridge hypothesis
`hStationaryToScaleZero : IsThermodynamicReadoutStationary ... → CI.chiralScale = 0`
from the new theorem surface while keeping the older compatibility theorem
available.
-/
@[rep_depth transport]
theorem semanticCollapsePacket_of_firstVariation_eq_zero_of_probeFaithful
    {P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)}
    {ψ : InfoGeometry.Krein.DoubledSpace E}
    {A : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E}
    (hFaithful : InfoGeometry.Canonical.ThermodynamicGenerator.ProbeFaithful (E := E) P)
    (hFirst :
      InfoGeometry.Canonical.RelativeModularPotential.firstVariation (E := E) P ψ A = 0)
    (hStationaryToScaleZero :
      InfoGeometry.Canonical.ThermodynamicGenerator.IsThermodynamicReadoutStationary
        (E := E) P ψ A → CI.chiralScale = 0)
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.chiralScale = 0
      ∧ CI.epsilon = 0
      ∧ CI.projectorObstruction = 0
      ∧ CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  exact
    semanticCollapsePacket_of_firstVariation_eq_zero_of_probeFaithful_of_stationaryScaleZeroWitness
      (CI := CI) hFaithful hFirst hStationaryToScaleZero hProj hLeft

end ConformalInference

end SouriauWeylClosure

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
    (V : SplitVielbein K x) (Γ : InfoGeometry.Canonical.RicciMongeAmpere.SpinConnection K x V)
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
