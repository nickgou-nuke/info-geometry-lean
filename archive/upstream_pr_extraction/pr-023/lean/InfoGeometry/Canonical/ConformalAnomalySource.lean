import Mathlib.Analysis.Complex.Trigonometric
import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Canonical.ChiralEinsteinBridge
import InfoGeometry.Canonical.GrandCanonicalExperts

namespace InfoGeometry.Canonical.ConformalUnification

open InfoGeometry.Canonical.ChiralEinsteinBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RicciMongeAmpere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ConformalInference

variable (CI : ConformalInference E)

/-- Canonical obstruction operator: the spectral/metric projector commutator. -/
noncomputable abbrev projectorObstruction : E →L[ℝ] E :=
  CI.chiralAnomalyOperator

section

/-- Exact operator identity for the projector obstruction. -/
theorem projectorObstruction_eq_commutator :
    CI.projectorObstruction =
      CI.spectralChiralProjector * CI.metricChiralProjector
        - CI.metricChiralProjector * CI.spectralChiralProjector := by
  simp [projectorObstruction, chiralAnomalyOperator, chiralAnomaly,
    spectralChiralProjector, metricChiralProjector]

end

/-- KKT operator bridge: under explicit wing hypotheses, the projector
obstruction operator is grade zero. -/
theorem projectorObstruction_isGZero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    InfoGeometry.Canonical.KKTCore.IsGZero X CI.projectorObstruction := by
  simpa [projectorObstruction] using
    CI.chiralAnomalyOperator_isGZero_of_kkt_wings
      (X := X) hA hAMP hAD

theorem projectorObstruction_gOnePart_eq_zero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    InfoGeometry.Canonical.KKTCore.gOnePart X CI.projectorObstruction = 0 := by
  simpa [projectorObstruction] using
    CI.chiralAnomalyOperator_gOnePart_eq_zero_of_kkt_wings
      (X := X) hA hAMP hAD

theorem projectorObstruction_gNegOnePart_eq_zero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    InfoGeometry.Canonical.KKTCore.gNegOnePart X CI.projectorObstruction = 0 := by
  simpa [projectorObstruction] using
    CI.chiralAnomalyOperator_gNegOnePart_eq_zero_of_kkt_wings
      (X := X) hA hAMP hAD

theorem projectorObstruction_eq_diagonal_blocks_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    CI.projectorObstruction
      = InfoGeometry.Canonical.KKTCore.plusProjector X * CI.projectorObstruction
          * InfoGeometry.Canonical.KKTCore.plusProjector X
        + InfoGeometry.Canonical.KKTCore.minusProjector X * CI.projectorObstruction
          * InfoGeometry.Canonical.KKTCore.minusProjector X := by
  simpa [projectorObstruction] using
    CI.chiralAnomalyOperator_eq_diagonal_blocks_of_kkt_wings
      (X := X) hA hAMP hAD

theorem projectorObstruction_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    InfoGeometry.Canonical.KKTCore.plusProjector X * CI.projectorObstruction
      * InfoGeometry.Canonical.KKTCore.minusProjector X = 0 := by
  simpa [projectorObstruction] using
    CI.chiralAnomalyOperator_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings
      (X := X) hA hAMP hAD

theorem projectorObstruction_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    InfoGeometry.Canonical.KKTCore.minusProjector X * CI.projectorObstruction
      * InfoGeometry.Canonical.KKTCore.plusProjector X = 0 := by
  simpa [projectorObstruction] using
    CI.chiralAnomalyOperator_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings
      (X := X) hA hAMP hAD

/-- Primary scalar readout of the noncommutative projector obstruction. -/
noncomputable def obstructionScale : ℝ :=
  ‖CI.projectorObstruction‖₊

/-- Legacy scalar compatibility alias. Prefer `obstructionScale`. -/
noncomputable abbrev epsilon : ℝ := CI.obstructionScale

/-- Compatibility alias for the anomaly scale. Prefer `obstructionScale`. -/
noncomputable abbrev chiralScale : ℝ := CI.obstructionScale

/-- Bounded scalar readout of the obstruction scale via `tanh`. -/
noncomputable def squashedObstructionScale : ℝ :=
  Real.tanh CI.obstructionScale

/--
Scalar coefficient used to feed the bounded squashed readout back into the
operator layer.
-/
noncomputable def projectorObstructionSquashCoeff : ℝ :=
  if _ : CI.obstructionScale = 0 then 0
  else CI.squashedObstructionScale / CI.obstructionScale

/--
Bounded operator-valued readout of the projector obstruction.

This keeps the operator support while using the bounded scalar readout as the
coefficient.
-/
noncomputable def squashedProjectorObstruction : E →L[ℝ] E :=
  CI.projectorObstructionSquashCoeff • CI.projectorObstruction

section

/-- Primary scalar bridge from the obstruction operator to its norm readout. -/
theorem obstructionScale_eq_projectorObstruction_norm :
    CI.obstructionScale =
      ‖CI.spectralChiralProjector * CI.metricChiralProjector
          - CI.metricChiralProjector * CI.spectralChiralProjector‖₊ := by
  rw [obstructionScale, CI.projectorObstruction_eq_commutator]

/-- Primary scalar bridge written through the obstruction-operator alias. -/
theorem obstructionScale_eq_projectorObstruction_nnnorm :
    CI.obstructionScale = ‖CI.projectorObstruction‖₊ := by
  rfl

/-- Primary operator-first readout: the obstruction-operator norm is the scalar readout. -/
theorem projectorObstruction_nnnorm_eq_obstructionScale :
    ‖CI.projectorObstruction‖₊ = CI.obstructionScale := by
  rfl

/-- Compatibility alias: `chiralScale` is the obstruction-scale readout. -/
theorem chiralScale_eq_obstructionScale :
    CI.chiralScale = CI.obstructionScale := by
  rfl

/-- Compatibility alias: scalar `epsilon` is the obstruction-scale readout. -/
theorem epsilon_eq_obstructionScale :
    CI.epsilon = CI.obstructionScale := by
  rfl

/--
Exact obstruction identity: the anomaly source scale is the norm of the
projector commutator.
-/
theorem chiralScale_eq_projectorObstruction_norm :
    CI.chiralScale =
      ‖CI.spectralChiralProjector * CI.metricChiralProjector
          - CI.metricChiralProjector * CI.spectralChiralProjector‖₊ := by
  simpa [CI.chiralScale_eq_obstructionScale] using
    CI.obstructionScale_eq_projectorObstruction_norm

/-- Scalar bridge written through the explicit obstruction operator alias. -/
theorem chiralScale_eq_projectorObstruction_nnnorm :
    CI.chiralScale = ‖CI.projectorObstruction‖₊ := by
  simpa [CI.chiralScale_eq_obstructionScale] using
    CI.obstructionScale_eq_projectorObstruction_nnnorm

/-- Operator-first bridge: the obstruction-operator norm is the chiral scale. -/
theorem projectorObstruction_nnnorm_eq_chiralScale :
    ‖CI.projectorObstruction‖₊ = CI.chiralScale := by
  simpa [CI.chiralScale_eq_obstructionScale] using
    CI.projectorObstruction_nnnorm_eq_obstructionScale

/-- The bounded scalar readout is exactly `tanh` of the primary scale. -/
theorem squashedObstructionScale_eq_tanh_obstructionScale :
    CI.squashedObstructionScale = Real.tanh CI.obstructionScale := by
  rfl

/-- If the primary scale vanishes, the squash coefficient vanishes. -/
@[simp] theorem projectorObstructionSquashCoeff_eq_zero_of_obstructionScale_eq_zero
    (hScaleZero : CI.obstructionScale = 0) :
    CI.projectorObstructionSquashCoeff = 0 := by
  simp [projectorObstructionSquashCoeff, hScaleZero]

/--
Away from zero scale, the squash coefficient is the bounded/readout ratio.
-/
theorem projectorObstructionSquashCoeff_eq_squashedObstructionScale_div_obstructionScale
    (hScaleNe : CI.obstructionScale ≠ 0) :
    CI.projectorObstructionSquashCoeff =
      CI.squashedObstructionScale / CI.obstructionScale := by
  simp [projectorObstructionSquashCoeff, hScaleNe]

/--
The squash coefficient sends the primary scale to the bounded scalar readout.
-/
theorem projectorObstructionSquashCoeff_mul_obstructionScale_eq_squashedObstructionScale :
    CI.projectorObstructionSquashCoeff * CI.obstructionScale =
      CI.squashedObstructionScale := by
  by_cases hScaleZero : CI.obstructionScale = 0
  · simp [projectorObstructionSquashCoeff, squashedObstructionScale, hScaleZero]
  · calc
      CI.projectorObstructionSquashCoeff * CI.obstructionScale
          = (CI.squashedObstructionScale / CI.obstructionScale) * CI.obstructionScale := by
              simp [projectorObstructionSquashCoeff, hScaleZero]
      _ = CI.squashedObstructionScale := by
            rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hScaleZero, mul_one]

/-- The squashed obstruction operator is defined by scalar rescaling. -/
theorem squashedProjectorObstruction_eq_smul_projectorObstruction :
    CI.squashedProjectorObstruction =
      CI.projectorObstructionSquashCoeff • CI.projectorObstruction := by
  rfl

/-- Vanishing obstruction forces vanishing squashed obstruction. -/
@[simp] theorem squashedProjectorObstruction_eq_zero_of_projectorObstruction_eq_zero
    (hObsZero : CI.projectorObstruction = 0) :
    CI.squashedProjectorObstruction = 0 := by
  simp [squashedProjectorObstruction, hObsZero]

/-- Zero primary scale forces vanishing squashed obstruction. -/
@[simp] theorem squashedProjectorObstruction_eq_zero_of_obstructionScale_eq_zero
    (hScaleZero : CI.obstructionScale = 0) :
    CI.squashedProjectorObstruction = 0 := by
  have hNorm : ‖CI.projectorObstruction‖₊ = 0 := by
    simpa [obstructionScale] using hScaleZero
  exact CI.squashedProjectorObstruction_eq_zero_of_projectorObstruction_eq_zero
    ((nnnorm_eq_zero).1 hNorm)

end

/-- Vanishing obstruction under explicit projector commutation. -/
theorem projectorObstruction_eq_zero_of_commute
    (hComm : Commute CI.spectralChiralProjector CI.metricChiralProjector) :
    CI.projectorObstruction = 0 := by
  exact CI.chiralAnomaly_eq_zero_of_projectors_commute hComm.eq

/-- Exact iff form: vanishing obstruction operator is equivalent to projector
commutation. -/
theorem projectorObstruction_eq_zero_iff_commute :
    CI.projectorObstruction = 0
      ↔ Commute CI.spectralChiralProjector CI.metricChiralProjector := by
  constructor
  · intro hObs
    simpa [Commute] using CI.projectors_commute_of_chiralAnomaly_eq_zero hObs
  · intro hComm
    exact CI.projectorObstruction_eq_zero_of_commute hComm

/-- Commuting projectors force zero anomaly source scale. -/
theorem chiralScale_eq_zero_of_projectors_commute
    (hComm :
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector) :
    CI.chiralScale = 0 := by
  have hAnomZero : CI.chiralAnomalyOperator = 0 :=
    CI.chiralAnomaly_eq_zero_of_projectors_commute hComm
  simp [obstructionScale, hAnomZero]

section

/-- Non-commuting projectors force nonzero anomaly source scale. -/
theorem chiralScale_ne_zero_of_projectors_not_commute
    (hCommNe :
      CI.spectralChiralProjector * CI.metricChiralProjector
        ≠ CI.metricChiralProjector * CI.spectralChiralProjector) :
    CI.chiralScale ≠ 0 := by
  intro hScaleZero
  have hNorm : ‖CI.chiralAnomalyOperator‖₊ = 0 := by
    simpa [obstructionScale, chiralAnomalyOperator] using hScaleZero
  have hAnomZero : CI.chiralAnomalyOperator = 0 := (nnnorm_eq_zero).1 hNorm
  exact hCommNe ((CI.chiralAnomalyOperator_eq_zero_iff_projectors_commute).1 hAnomZero)

end

/--
Constructive projector-commutation closure from scalar anomaly-driven Kähler-Ricci
dynamics at normalized RG fixed point.

This discharges commutation without assuming it directly:
the dynamics force `flow = 0` and `flow = chiralScale`, hence `chiralScale = 0`,
which forces vanishing anomaly and therefore projector commutation.
-/
private theorem projectors_commute_of_anomalyDriven_normalized_fixedpoint
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = 0)
    (hAnomFlow :
      SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow
        (fun _ => CI.chiralScale)) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector := by
  have hFlowZero : ∀ s : ℝ, flow s = 0 :=
    normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := E) (flow := flow) hNorm hFixed
  have hFlowTracksScale : ∀ s : ℝ, flow s = CI.chiralScale :=
    anomalyDrivenScalarRicci_fixedpoint_tracks_source
      (E := E) (flow := flow) (A := fun _ => CI.chiralScale)
      hAnomFlow hFixed
  have hScaleZero : CI.chiralScale = 0 := by
    calc
      CI.chiralScale = flow 0 := by simpa using (hFlowTracksScale 0).symm
      _ = 0 := hFlowZero 0
  have hNormAnom : ‖CI.chiralAnomalyOperator‖₊ = 0 := by
    simpa [obstructionScale, chiralAnomalyOperator] using hScaleZero
  have hAnomZero : CI.chiralAnomalyOperator = 0 :=
    (nnnorm_eq_zero).1 hNormAnom
  exact CI.projectors_commute_of_chiralAnomaly_eq_zero hAnomZero

section

private theorem anomalyDrivenScalarRicciFlow_of_normalized_and_chiralScale_zero
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hScaleZero : CI.chiralScale = 0) :
    SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow (fun _ => CI.chiralScale) := by
  have hZeroSource :
      SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow (fun _ => 0) :=
    (anomalyDriven_zeroSource_iff_normalized (E := E) (flow := flow)).2 hNorm
  intro s
  simpa [hScaleZero] using hZeroSource s

end
section

/--
Proof-carrying unit relative-volume witness for the RN/Kähler/log-det lane in
this conformal owner module.
-/
structure UnitRelativeVolumeWitness (n : Nat) (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n) : Prop where
  unit_relative_volume : relativeVolumeChangeRN n M = 1

/--
Normality (`ε = 0`) from the Kähler/log-det layer:
if the conformal chiral scale matches the RN Kähler potential and the RN
relative volume is unit, then `ε = 0`.
-/
theorem chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.chiralScale = 0 := by
  have hNegKZero : -kahlerPotentialRN n M = 0 := by
    have hLog :
        Real.log (relativeVolumeChangeRN n M) = Real.log (1 : ℝ) :=
      congrArg Real.log hUnitVolume
    simpa [relativeVolumeChangeRN] using hLog
  have hKZero : kahlerPotentialRN n M = 0 := by
    have h := congrArg Neg.neg hNegKZero
    simpa using h
  calc
    CI.chiralScale = kahlerPotentialRN n M := hScaleFromKahler
    _ = 0 := hKZero

/--
Proof-carrying unit-relative-volume route for scalar normality.

This constructive companion removes the bare
`relativeVolumeChangeRN n M = 1` hypothesis from the scalar zero-scale branch
when callers already own the `UnitRelativeVolumeBit` witness packet.
-/
theorem chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolumeBit
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeWitness n M) :
    CI.chiralScale = 0 := by
  exact CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
    (M := M) hScaleFromKahler bit.unit_relative_volume

end

/--
Zero anomaly scale implies projector commutation.

This gives a direct algebraic closure path from scalar normality (`χ = 0`)
to vanishing projector obstruction.
-/
theorem projectors_commute_of_chiralScale_eq_zero
    (hScaleZero : CI.chiralScale = 0) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector := by
  have hNormAnom : ‖CI.chiralAnomalyOperator‖₊ = 0 := by
    simpa [obstructionScale, chiralAnomalyOperator] using hScaleZero
  have hAnomZero : CI.chiralAnomalyOperator = 0 :=
    (nnnorm_eq_zero).1 hNormAnom
  exact CI.projectors_commute_of_chiralAnomaly_eq_zero hAnomZero

/--
Constructive iff route between scalar zero anomaly and projector commutation.

This packages the existing obstruction-operator owner theorem so downstream
users can consume the canonical `Commute` witness instead of carrying a bare
multiplication equality hypothesis.
-/
theorem chiralScale_eq_zero_iff_projectors_commute :
    CI.chiralScale = 0
      ↔ Commute CI.spectralChiralProjector CI.metricChiralProjector := by
  constructor
  · intro hScaleZero
    have hObsNorm : ‖CI.projectorObstruction‖₊ = 0 := by
      simpa [CI.chiralScale_eq_projectorObstruction_nnnorm] using hScaleZero
    exact (CI.projectorObstruction_eq_zero_iff_commute).1
      ((nnnorm_eq_zero).1 hObsNorm)
  · intro hComm
    have hObsZero : CI.projectorObstruction = 0 :=
      CI.projectorObstruction_eq_zero_of_commute hComm
    simp [chiralScale, obstructionScale, hObsZero]

/--
If the Drazin spectral projector commutes with the Moore-Penrose right
projector and the scalar chiral source vanishes, then the spectral projector
commutes with the conformal dilation generator.
-/
theorem spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D)
    (hScaleZero : CI.chiralScale = 0) :
    CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  have hNormObs : ‖CI.projectorObstruction‖₊ = 0 := by
    simpa [CI.chiralScale_eq_projectorObstruction_nnnorm] using hScaleZero
  have hNormAnom : ‖CI.chiralAnomalyOperator‖₊ = 0 := by
    simpa [projectorObstruction] using hNormObs
  have hAnomZero : CI.chiralAnomalyOperator = 0 :=
    (nnnorm_eq_zero).1 hNormAnom
  exact
    CI.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralAnomaly_eq_zero
      hRight hAnomZero

/--
Operator-first dilation/anomaly bridge:
if the Drazin spectral projector commutes with the Moore-Penrose right
projector, the dilation commutator is exactly minus one half of the
projector-obstruction operator.
-/
theorem spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_of_rightProjector_commute
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D
      = -((2 : ℝ)⁻¹) • CI.projectorObstruction := by
  simpa [projectorObstruction] using
    CI.spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_rightProjector_commute
      hRight

/--
Structured operator-first dilation/anomaly bridge:
under Moore-Penrose projector agreement and left-metric commutation, the
dilation commutator is exactly minus one half of the projector-obstruction
operator.
-/
theorem spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_of_projectorAgreement_of_metricProjector_commute
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D
      = -((2 : ℝ)⁻¹) • CI.projectorObstruction := by
  simpa [projectorObstruction] using
    CI.spectralProjector_commutator_dilation_eq_neg_half_anomaly_of_projectorAgreement_of_metricProjector_commute
      hProj hLeft

/--
The bounded squashed obstruction inherits grade-zero structure from the
unsquashed obstruction under the same KKT wing hypotheses.
-/
theorem squashedProjectorObstruction_isGZero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    InfoGeometry.Canonical.KKTCore.IsGZero X CI.squashedProjectorObstruction := by
  exact InfoGeometry.Canonical.KKTCore.isGZero_smul
    X CI.projectorObstructionSquashCoeff
    (CI.projectorObstruction_isGZero_of_kkt_wings (X := X) hA hAMP hAD)

/--
The bounded squashed obstruction remains block-diagonal in the KKT split.
-/
theorem squashedProjectorObstruction_eq_diagonal_blocks_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    CI.squashedProjectorObstruction
      = InfoGeometry.Canonical.KKTCore.plusProjector X * CI.squashedProjectorObstruction
          * InfoGeometry.Canonical.KKTCore.plusProjector X
        + InfoGeometry.Canonical.KKTCore.minusProjector X * CI.squashedProjectorObstruction
          * InfoGeometry.Canonical.KKTCore.minusProjector X := by
  exact InfoGeometry.Canonical.KKTCore.eq_diagonal_blocks_of_isGZero
    X (CI.squashedProjectorObstruction_isGZero_of_kkt_wings (X := X) hA hAMP hAD)

/--
The bounded squashed obstruction has vanishing off-diagonal `(+,-)` block in
the KKT split.
-/
theorem squashedProjectorObstruction_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    InfoGeometry.Canonical.KKTCore.plusProjector X * CI.squashedProjectorObstruction
      * InfoGeometry.Canonical.KKTCore.minusProjector X = 0 := by
  exact InfoGeometry.Canonical.KKTCore.plusProjector_mul_mul_minusProjector_eq_zero_of_isGZero
    X (CI.squashedProjectorObstruction_isGZero_of_kkt_wings (X := X) hA hAMP hAD)

/--
The bounded squashed obstruction has vanishing off-diagonal `(-,+)` block in
the KKT split.
-/
theorem squashedProjectorObstruction_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : InfoGeometry.Canonical.KKTCore.IsGOne X CI.A)
    (hAMP : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_MP)
    (hAD : InfoGeometry.Canonical.KKTCore.IsGNegOne X CI.A_D) :
    InfoGeometry.Canonical.KKTCore.minusProjector X * CI.squashedProjectorObstruction
      * InfoGeometry.Canonical.KKTCore.plusProjector X = 0 := by
  exact InfoGeometry.Canonical.KKTCore.minusProjector_mul_mul_plusProjector_eq_zero_of_isGZero
    X (CI.squashedProjectorObstruction_isGZero_of_kkt_wings (X := X) hA hAMP hAD)

/--
Specialized zero corollary from the operator-first dilation/anomaly bridge.
-/
theorem spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_projectorObstruction_eq_zero
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D)
    (hObsZero : CI.projectorObstruction = 0) :
    CI.P_D * CI.D - CI.D * CI.P_D = 0 := by
  simpa [projectorObstruction] using
    CI.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralAnomaly_eq_zero
      hRight hObsZero

/--
Projector commutation directly from the Kähler/log-det layer:
matching `χ` to the RN Kähler potential and unit relative volume force
`χ = 0`, hence vanishing projector obstruction.
-/
theorem projectors_commute_of_kahlerLogDet_unitRelativeVolume
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector := by
  exact CI.projectors_commute_of_chiralScale_eq_zero
    (CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume)

/--
Proof-carrying unit-relative-volume route for projector commutation.

This removes the bare `relativeVolumeChangeRN n M = 1` hypothesis from the
projector-closure lane when callers already own the compact
`UnitRelativeVolumeWitness` packet.
-/
theorem projectors_commute_of_kahlerLogDet_unitRelativeVolumeBit
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeWitness n M) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector := by
  exact CI.projectors_commute_of_kahlerLogDet_unitRelativeVolume
    (M := M) hScaleFromKahler bit.unit_relative_volume

/--
Log-det barrier self-concordance mechanics package:
unit relative volume in the RN layer forces zero Kähler potential, zero anomaly
scale, normal inference, and projector-obstruction closure.
-/
theorem logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    kahlerPotentialRN n M = 0
      ∧ CI.chiralScale = 0
      ∧ (CI.spectralChiralProjector * CI.metricChiralProjector
            = CI.metricChiralProjector * CI.spectralChiralProjector) := by
  have hScaleZero : CI.chiralScale = 0 :=
    CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  have hKahlerZero : kahlerPotentialRN n M = 0 := by
    calc
      kahlerPotentialRN n M = CI.chiralScale := by
        simpa [eq_comm] using hScaleFromKahler
      _ = 0 := hScaleZero
  refine ⟨hKahlerZero, hScaleZero, ?_⟩
  exact CI.projectors_commute_of_chiralScale_eq_zero hScaleZero

/--
Proof-carrying self-concordance mechanics route using the compact
`UnitRelativeVolumeWitness` packet instead of a bare unit-volume equality.
-/
theorem logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolumeBit
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeWitness n M) :
    kahlerPotentialRN n M = 0
      ∧ CI.chiralScale = 0
      ∧ (CI.spectralChiralProjector * CI.metricChiralProjector
            = CI.metricChiralProjector * CI.spectralChiralProjector) := by
  exact CI.logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume
    (M := M) hScaleFromKahler bit.unit_relative_volume

section

/--
Canonical anomaly-flow derivation from the Kähler/log-det layer.

This discharges the anomaly-flow witness directly from normalized Kähler-Ricci
flow and unit relative volume in the log-det potential layer.
-/
theorem anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow
      (fun _ => CI.chiralScale) := by
  have hScaleZero : CI.chiralScale = 0 :=
    CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  exact CI.anomalyDrivenScalarRicciFlow_of_normalized_and_chiralScale_zero
    (flow := flow) hNorm hScaleZero

/--
Proof-carrying anomaly-flow discharge using the compact
`UnitRelativeVolumeWitness` packet instead of a bare unit-volume equality.
-/
theorem anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized_unitRelativeVolumeBit
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeWitness n M) :
    SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow
      (fun _ => CI.chiralScale) := by
  exact CI.anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized
    (flow := flow) hNorm (M := M) hScaleFromKahler bit.unit_relative_volume

end

/--
Projector commutation from normalized Kähler/log-det data at a scalar Ricci
fixed point.

This discharges the anomaly-flow witness internally:
`hAnomFlow` is derived from the Kähler/log-det layer and then fed into the
fixed-point commutation closure.
-/
theorem projectors_commute_of_kahlerLogDet_normalized_fixedpoint
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = 0)
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector := by
  have hAnomFlow :
      SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow
        (fun _ => CI.chiralScale) :=
    CI.anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized
      (flow := flow) hNorm (M := M) hScaleFromKahler hUnitVolume
  exact CI.projectors_commute_of_anomalyDriven_normalized_fixedpoint
    (flow := flow) hNorm hFixed hAnomFlow

/--
Proof-carrying normalized fixed-point projector-commutation route using the
compact `UnitRelativeVolumeWitness` packet instead of a bare unit-volume
hypothesis.
-/
theorem projectors_commute_of_kahlerLogDet_normalized_fixedpoint_unitRelativeVolumeBit
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = 0)
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeWitness n M) :
    CI.spectralChiralProjector * CI.metricChiralProjector
      = CI.metricChiralProjector * CI.spectralChiralProjector := by
  have hAnomFlow :
      SatisfiesAnomalyDrivenScalarRicciFlow (E := E) flow
        (fun _ => CI.chiralScale) :=
    CI.anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized_unitRelativeVolumeBit
      (flow := flow) hNorm (M := M) hScaleFromKahler bit
  exact CI.projectors_commute_of_anomalyDriven_normalized_fixedpoint
    (flow := flow) hNorm hFixed hAnomFlow

section

theorem einsteinEquation_of_projectorObstruction_source
    (c : ℝ) (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CI.chiralScale)) Λ κ
      (anomalyStressEnergyAt Kgeo x CI.chiralScale) := by
  exact einsteinEquation_of_anomaly_source
    (E := E)
    (c := c) (R := R) (K := Kgeo) (x := x)
    (Λ := Λ) (κ := κ) (A := CI.chiralScale) hEin

end

/--
Cartan-like Decomposition of the Information Manifold.
The space decomposes into a Normal sector (ε = 0) and a Chiral sector (ε > 0).
This mirrors the Cl(1,1) grading into even and odd endomorphisms.
-/
def IsNormalInference : Prop := CI.chiralScale = 0

/--
Normal-inference corollary from the log-det self-concordance mechanics package.
-/
theorem isNormalInference_of_logDetBarrier_selfConcordance_mechanics
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    IsNormalInference (CI := CI) := by
  have hMechanics :=
    CI.logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  simpa [IsNormalInference] using hMechanics.2.1

/-- Definition `IsChiralInference`. -/
def IsChiralInference : Prop := 0 < CI.chiralScale

-- Legacy alias: normal inference stated via `epsilon = 0`.
section

/-- Theorem `isNormalInference_iff_epsilon_eq_zero`. -/
theorem isNormalInference_iff_epsilon_eq_zero :
    IsNormalInference (CI := CI) ↔ CI.epsilon = 0 := by
  simp [IsNormalInference, chiralScale]

-- Legacy alias: chiral inference stated via `0 < epsilon`.
/-- Theorem `isChiralInference_iff_epsilon_pos`. -/
theorem isChiralInference_iff_epsilon_pos :
    IsChiralInference (CI := CI) ↔ 0 < CI.epsilon := by
  simp [IsChiralInference, chiralScale]

end

/--
Zero anomaly follows from the normalized Kähler/log-det flow assumptions used
to derive projector commutation.
-/
theorem chiralAnomaly_eq_zero_of_kahlerLogDet_normalized_fixedpoint
    (flow : ScalarRicciFlow E)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = 0)
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.chiralAnomalyOperator = 0 := by
  have hComm :
      CI.spectralChiralProjector * CI.metricChiralProjector
        = CI.metricChiralProjector * CI.spectralChiralProjector :=
    CI.projectors_commute_of_kahlerLogDet_normalized_fixedpoint
      (flow := flow) hNorm hFixed (M := M) hScaleFromKahler hUnitVolume
  exact CI.chiralAnomaly_eq_zero_of_projectors_commute hComm

/--
The Structure Constant Operator (Σ).
Defined as the commutator of the spectral (Drazin) and metric (Penrose) projectors.
This operator sets the scale for the non-commutative deformation of the
information volume form.
-/
def actionStructureConstantOp : E →L[ℝ] E :=
  CI.P_D.comp CI.P_MP - CI.P_MP.comp CI.P_D

/--
The Scalar Unit of Action (h).
The operator norm of the structure constant operator.
This sets the fundamental 'grain' or 'scale' of the information manifold.
-/
noncomputable def unitOfAction : ℝ :=
  ‖CI.actionStructureConstantOp‖

section

/-- The structure-constant operator is exactly the chiral-anomaly operator. -/
theorem actionStructureConstantOp_eq_chiralAnomalyOperator :
    CI.actionStructureConstantOp = CI.chiralAnomalyOperator := by
  ext x
  rfl

end

section

/-- The scalar unit of action is the same primary obstruction-scale readout. -/
theorem unitOfAction_eq_obstructionScale :
    CI.unitOfAction = CI.obstructionScale := by
  simp [unitOfAction, obstructionScale, CI.actionStructureConstantOp_eq_chiralAnomalyOperator]

/-- The scalar unit of action coincides with the chiral anomaly scale. -/
theorem unitOfAction_eq_chiralScale :
    CI.unitOfAction = CI.chiralScale := by
  calc
    CI.unitOfAction = CI.obstructionScale := CI.unitOfAction_eq_obstructionScale
    _ = CI.chiralScale := by rfl

end

section

/--
Constructive unit-of-action collapse from the RN/Kähler/log-det lane.

This packages the owner route
`unitOfAction = chiralScale = kahlerPotentialRN = 0` once the caller already
owns the unit-relative-volume witness on the infinite/operatorial lane.
-/
theorem unitOfAction_eq_zero_of_kahlerLogDet_unitRelativeVolume
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.unitOfAction = 0 := by
  rw [CI.unitOfAction_eq_chiralScale]
  exact CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
    (M := M) hScaleFromKahler hUnitVolume

/--
Constructive unit-of-action collapse using the proof-carrying
`UnitRelativeVolumeWitness` packet instead of a bare unit-volume equality.
-/
theorem unitOfAction_eq_zero_of_kahlerLogDet_unitRelativeVolumeBit
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeWitness n M) :
    CI.unitOfAction = 0 := by
  exact CI.unitOfAction_eq_zero_of_kahlerLogDet_unitRelativeVolume
    (M := M) hScaleFromKahler bit.unit_relative_volume

/-- In the normal phase, the unit of action vanishes. -/
theorem unitOfAction_eq_zero_of_normalInference
    (hNormal : IsNormalInference (CI := CI)) :
    CI.unitOfAction = 0 := by
  rw [CI.unitOfAction_eq_chiralScale]
  exact hNormal

/-- In the chiral phase, the unit of action is strictly positive. -/
theorem unitOfAction_pos_of_chiralInference
    (hChiral : IsChiralInference (CI := CI)) :
    0 < CI.unitOfAction := by
  rw [CI.unitOfAction_eq_chiralScale]
  exact hChiral

end

section

theorem unitOfAction_pos_of_noncommute
    (hAnom : CI.P_D.comp CI.P_MP ≠ CI.P_MP.comp CI.P_D) :
    0 < CI.unitOfAction := by
  unfold unitOfAction actionStructureConstantOp
  simp only [norm_pos_iff, ne_eq]
  exact sub_ne_zero.mpr hAnom

end


section

/--
Constructive bridge from the RN/Kahler/log-det lane into the normal phase.
-/
theorem isNormalInference_of_kahlerLogDet_unitRelativeVolume
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.IsNormalInference := by
  have hZero :=
    CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  simpa [ConformalInference.IsNormalInference] using hZero

/--
Constructive bridge from the RN/Kahler/log-det lane into the normal phase via
the proof-carrying unit-relative-volume packet.
-/
theorem isNormalInference_of_kahlerLogDet_unitRelativeVolumeBit
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeWitness n M) :
    CI.IsNormalInference := by
  have hZero :=
    CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolumeBit
      (M := M) hScaleFromKahler bit
  simpa [ConformalInference.IsNormalInference] using hZero

end

/--
Constructive zero-anomaly endpoint at unit relative volume.
-/
theorem chiralAnomalyOperator_eq_zero_of_unitRelativeVolume
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (hUnitVolume : relativeVolumeChangeRN n M = 1) :
    CI.chiralAnomalyOperator = 0 := by
  have hCommute :=
    CI.projectors_commute_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  exact CI.chiralAnomaly_eq_zero_of_projectors_commute hCommute

/--
Constructive zero-anomaly endpoint using the proof-carrying
`UnitRelativeVolumeWitness` packet instead of a bare unit-volume equality.
-/
theorem chiralAnomalyOperator_eq_zero_of_unitRelativeVolumeBit
    {n : Nat}
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = kahlerPotentialRN n M)
    (bit : UnitRelativeVolumeWitness n M) :
    CI.chiralAnomalyOperator = 0 := by
  exact CI.chiralAnomalyOperator_eq_zero_of_unitRelativeVolume
    (M := M) hScaleFromKahler bit.unit_relative_volume

end ConformalInference

namespace CertifiedInverseKernel

variable (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E)

/--
Certified-kernel Einstein source closure.

This is the owner-path gravity bridge: the Einstein source equation is derived
from the canonical certified inverse-kernel package via the conformal adapter,
without introducing a separate bridge payload.
-/
theorem einsteinEquation_of_projectorObstruction_source
    (c : ℝ) (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    EinsteinEquationAt R Kgeo x (2 * (c + Λ - κ * CIK.chiralScale)) Λ κ
      (anomalyStressEnergyAt Kgeo x CIK.chiralScale) := by
  simpa [InfoGeometry.Canonical.ConformalUnification.CertifiedInverseKernel.toConformalInference]
    using
      (ConformalInference.einsteinEquation_of_projectorObstruction_source
        (CI := InfoGeometry.Canonical.ConformalUnification.CertifiedInverseKernel.toConformalInference CIK)
        (c := c) (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) hEin)

end CertifiedInverseKernel

namespace CertifiedConformalInference

variable (CCI : InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference E)

/-- Certified-conformal Einstein source closure routed through the certified
inverse-kernel owner package. -/
theorem einsteinEquation_of_projectorObstruction_source
    (c : ℝ) (R : RicciTensor E)
    (Kgeo : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (Λ κ : ℝ)
    (hEin : IsEinsteinKaehlerAtWith c R Kgeo x) :
    EinsteinEquationAt R Kgeo x
        (2 * (c + Λ - κ * CCI.toConformalInference.chiralScale)) Λ κ
        (anomalyStressEnergyAt Kgeo x CCI.toConformalInference.chiralScale) := by
  simpa [InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.toCertifiedInverseKernel,
      InfoGeometry.Canonical.ConformalUnification.CertifiedInverseKernel.toConformalInference]
    using
      (CertifiedInverseKernel.einsteinEquation_of_projectorObstruction_source
        (CIK := CCI.toCertifiedInverseKernel)
        (c := c) (R := R) (Kgeo := Kgeo) (x := x) (Λ := Λ) (κ := κ) hEin)

end CertifiedConformalInference

end InfoGeometry.Canonical.ConformalUnification
