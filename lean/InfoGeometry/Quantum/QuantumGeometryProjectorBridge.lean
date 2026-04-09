import InfoGeometry.Canonical.EinsteinAnomalyOperator
import InfoGeometry.Canonical.QuantumGeometryDualSheetBridge
import InfoGeometry.Canonical.StateDependentTransport
import InfoGeometry.Quantum.GeometricTensorOperatorLift
import InfoGeometry.Quantum.WeldedProjectorCorrelationBridge

open scoped InnerProductSpace

namespace InfoGeometry.Quantum

open InfoGeometry.Convex
open InfoGeometry.Krein
open InfoGeometry.Canonical.BeliefDynamics
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.MongeAmpereDualSheetBridge
open InfoGeometry.Canonical.ModularTwoStateCorrelation
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Quantum.GeometricQuantumTensor

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Primary noncommutative owner pair for the quantum-geometry / projector-obstruction
bridge on doubled space.

The first component is the doubled quantum-geometry metric operator.
The second component is the lifted projector-obstruction operator.
-/
noncomputable def quantumGeometryProjectorOperatorPair
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E) : EndH × EndH :=
  ( dualSheetLift (E := E) (quantumGeometryOp H x)
  , SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator )

@[simp] theorem fst_quantumGeometryProjectorOperatorPair
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E) :
    (quantumGeometryProjectorOperatorPair (E := E) H x SCI).1
      =
    dualSheetLift (E := E) (quantumGeometryOp H x) := rfl

@[simp] theorem snd_quantumGeometryProjectorOperatorPair
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E) :
    (quantumGeometryProjectorOperatorPair (E := E) H x SCI).2
      =
    SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator := rfl

@[simp] theorem plusProjectorFlux_fst_quantumGeometryProjectorOperatorPair
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E) :
    InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux
        ((quantumGeometryProjectorOperatorPair (E := E) H x SCI).1)
      = 0 := by
  simp [quantumGeometryProjectorOperatorPair]

@[simp] theorem minusProjectorFlux_fst_quantumGeometryProjectorOperatorPair
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E) :
    InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux
        ((quantumGeometryProjectorOperatorPair (E := E) H x SCI).1)
      = 0 := by
  simp [quantumGeometryProjectorOperatorPair]

@[simp] theorem plusProjectorFlux_snd_quantumGeometryProjectorOperatorPair
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E) :
    InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux
        ((quantumGeometryProjectorOperatorPair (E := E) H x SCI).2)
      = 0 := by
  change InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux
      SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator = 0
  have hFlux :
      InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux
          SCI.toCertifiedConformalInference.liftedLeftChiralAnomalyOperator = 0 :=
    SCI.toCertifiedConformalInference.plusProjectorFlux_liftedChiralAnomalyOperator
  simpa [InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedProjectorObstructionOperator,
    InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedLeftChiralAnomalyOperator] using hFlux

@[simp] theorem minusProjectorFlux_snd_quantumGeometryProjectorOperatorPair
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E) :
    InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux
        ((quantumGeometryProjectorOperatorPair (E := E) H x SCI).2)
      = 0 := by
  change InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux
      SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator = 0
  have hFlux :
      InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux
          SCI.toCertifiedConformalInference.liftedLeftChiralAnomalyOperator = 0 :=
    SCI.toCertifiedConformalInference.minusProjectorFlux_liftedChiralAnomalyOperator
  simpa [InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedProjectorObstructionOperator,
    InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedLeftChiralAnomalyOperator] using hFlux

/--
Operator-level bridge: under projector agreement, the phase half of the bridge is
exactly the metric readout of the second operator in the noncommutative owner pair.
-/
theorem weldedProjectorObstructionStatePhaseReadout_eq_metricOfOperator_snd_quantumGeometryProjectorOperatorPair_of_projectorAgreement
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E) (ψ : H₂)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    weldedProjectorObstructionStatePhaseReadout (E := E) SCI ψ
      =
    metricOfOperator (E := E)
      ((quantumGeometryProjectorOperatorPair (E := E) H x SCI).2) := by
  simpa [quantumGeometryProjectorOperatorPair] using
    weldedProjectorObstructionStatePhaseReadout_eq_projectorObstructionMetric_of_projectorAgreement
      (E := E) SCI ψ hProj

/--
Primary operator-level pair of readout forms for the bridge:
both metric and phase are expressed as readouts of noncommutative operators.
-/
theorem quantumGeometryMetric_and_weldedProjectorPhase_eq_metricOfOperator_pair_of_projectorAgreement
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E) (ψ : H₂)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    ( metricOfOperator
        ((quantumGeometryProjectorOperatorPair (E := E) H x SCI).1)
    , weldedProjectorObstructionStatePhaseReadout (E := E) SCI ψ )
      =
    ( metricOfOperator
        ((quantumGeometryProjectorOperatorPair (E := E) H x SCI).1)
    , metricOfOperator
        ((quantumGeometryProjectorOperatorPair (E := E) H x SCI).2) ) := by
  apply Prod.ext
  · rfl
  · exact
      weldedProjectorObstructionStatePhaseReadout_eq_metricOfOperator_snd_quantumGeometryProjectorOperatorPair_of_projectorAgreement
        (E := E) (H := H) (x := x) (SCI := SCI) (ψ := ψ) hProj

/--
Dynamic noncommutative owner pair:
the metric operator is transported by relative-modular conjugation, while the
phase-side anomaly operator is transported by the certified Bogoliubov
conjugation owner.
-/
noncomputable def quantumGeometryEinsteinTransportedOperatorPair
    (H : HessianGeometry E) (x : E)
    (CCI : CertifiedConformalInference E) (hMod : EndH) (t : ℝ) : EndH × EndH :=
  ( InfoGeometry.Canonical.expTransport
      (A := EndH)
      (relativeModularKGenerator (E := E) hMod)
      (dualSheetLift (E := E) (quantumGeometryOp H x))
      t
  , CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator hMod t )

/--
The metric-side component of the transported operator pair has infinitesimal
velocity equal to the relative-modular derivation of the doubled
quantum-geometry operator.
-/
theorem deriv_fst_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_relativeModularDeriv
    (H : HessianGeometry E) (x : E)
    (CCI : CertifiedConformalInference E) (hMod : EndH) :
    deriv
      (fun t => (quantumGeometryEinsteinTransportedOperatorPair
        H x CCI hMod t).1)
      0
      =
    relativeModularDeriv (E := E) hMod
      (dualSheetLift (E := E) (quantumGeometryOp H x)) := by
  simpa [quantumGeometryEinsteinTransportedOperatorPair,
    relativeModularKGenerator, relativeModularDeriv] using
    (InfoGeometry.Canonical.deriv_expTransport_at_zero
      (A := EndH)
      (X := relativeModularKGenerator (E := E) hMod)
      (A₀ := dualSheetLift (E := E) (quantumGeometryOp H x)))

/--
If the gauge channel commutes with the doubled quantum-geometry operator, the
metric-side transport is purely source-driven at `t = 0`.
-/
theorem deriv_fst_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_relativeModularSourceDeriv_of_commute_gaugePart
    (H : HessianGeometry E) (x : E)
    (CCI : CertifiedConformalInference E) (hMod : EndH)
    (hCommGauge :
      Commute
        (dualSheetLift (E := E) (quantumGeometryOp H x))
        (modularGeneratorGaugePart (E := E) hMod)) :
    deriv
      (fun t => (quantumGeometryEinsteinTransportedOperatorPair
        H x CCI hMod t).1)
      0
      =
    relativeModularSourceDeriv (E := E) hMod
      (dualSheetLift (E := E) (quantumGeometryOp H x)) := by
  rw [deriv_fst_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_relativeModularDeriv
    (H := H) (x := x) (CCI := CCI) (hMod := hMod)]
  exact relativeModularDeriv_eq_relativeModularSourceDeriv_of_commute_gaugePart
    (E := E) hMod (dualSheetLift (E := E) (quantumGeometryOp H x)) hCommGauge

/--
If the gauge channel commutes with the lifted Einstein anomaly operator, the
phase-side transport is purely source-driven at `t = 0`.
-/
theorem deriv_snd_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_relativeModularSourceDeriv_of_commute_gaugePart
    (H : HessianGeometry E) (x : E)
    (CCI : CertifiedConformalInference E) (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod)) :
    deriv
      (fun t => (quantumGeometryEinsteinTransportedOperatorPair
        H x CCI hMod t).2)
      0
      =
    relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator := by
  simpa [quantumGeometryEinsteinTransportedOperatorPair] using
    CCI.deriv_bogoliubovConjugate_liftedEinsteinAnomalyOperator_at_zero_eq_relativeModularSourceDeriv_of_commute_gaugePart
      hMod hCommGauge

/--
Readout-level transport package for the dynamic noncommutative owner pair:
under gauge commutation on both components, the infinitesimal transported
metric readouts are exactly the metric readouts of the corresponding
relative-modular source derivatives.
-/
theorem deriv_metricOfOperator_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_metricOf_relativeModularSourceDeriv_pair_of_commute_gaugePart
    (H : HessianGeometry E) (x : E)
    (CCI : CertifiedConformalInference E) (hMod : EndH)
    (u v : H₂)
    (hCommGaugeMetric :
      Commute
        (dualSheetLift (E := E) (quantumGeometryOp H x))
        (modularGeneratorGaugePart (E := E) hMod))
    (hCommGaugePhase :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod)) :
    ( deriv
        (fun t =>
          metricOfOperator
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).1)
            u v)
        0
    , deriv
        (fun t =>
          metricOfOperator
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).2)
            u v)
        0 )
      =
    ( metricOfOperator
        (relativeModularSourceDeriv (E := E) hMod
          (dualSheetLift (E := E) (quantumGeometryOp H x)))
        u v
    , metricOfOperator
        (relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
        u v ) := by
  apply Prod.ext
  · simpa [quantumGeometryEinsteinTransportedOperatorPair] using
      deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
        (E := E) hMod (dualSheetLift (E := E) (quantumGeometryOp H x)) hCommGaugeMetric u v
  · simpa [quantumGeometryEinsteinTransportedOperatorPair] using
      deriv_metricOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
        (E := E) CCI hMod hCommGaugePhase u v

/--
Berry-readout transport package for the dynamic noncommutative owner pair:
under gauge commutation on both components, the infinitesimal transported Berry
readouts are exactly the Berry readouts of the corresponding
relative-modular source derivatives.
-/
theorem deriv_berryOfOperator_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_berryOf_relativeModularSourceDeriv_pair_of_commute_gaugePart
    (H : HessianGeometry E) (x : E)
    (CCI : CertifiedConformalInference E) (hMod : EndH)
    (u v : H₂)
    (hCommGaugeMetric :
      Commute
        (dualSheetLift (E := E) (quantumGeometryOp H x))
        (modularGeneratorGaugePart (E := E) hMod))
    (hCommGaugePhase :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod)) :
    ( deriv
        (fun t =>
          berryOfOperator
            (E := E)
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).1)
            u v)
        0
    , deriv
        (fun t =>
          berryOfOperator
            (E := E)
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).2)
            u v)
        0 )
      =
    ( berryOfOperator
        (E := E)
        (relativeModularSourceDeriv (E := E) hMod
          (dualSheetLift (E := E) (quantumGeometryOp H x)))
        u v
    , berryOfOperator
        (E := E)
        (relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
        u v ) := by
  apply Prod.ext
  · simpa [quantumGeometryEinsteinTransportedOperatorPair] using
      deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_relativeModularSourceDeriv_of_commute_gaugePart
        (E := E) hMod (dualSheetLift (E := E) (quantumGeometryOp H x)) hCommGaugeMetric u v
  · simpa [quantumGeometryEinsteinTransportedOperatorPair] using
      deriv_berryOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_berryOf_relativeModularSourceDeriv_of_commute_gaugePart
        (E := E) CCI hMod hCommGaugePhase u v

/--
`Jε`-Berry two-form transport package for the dynamic noncommutative owner pair:
under gauge commutation on both components, the infinitesimal transported
split-`Cl(1,1)` phase readouts are exactly the `Jε`-Berry readouts of the
corresponding relative-modular source derivatives.
-/
theorem deriv_berryTwoFormJEpsOfOperator_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_berryTwoFormJEpsOf_relativeModularSourceDeriv_pair_of_commute_gaugePart
    (H : HessianGeometry E) (x : E)
    (CCI : CertifiedConformalInference E) (hMod : EndH)
    (u v : H₂)
    (hCommGaugeMetric :
      Commute
        (dualSheetLift (E := E) (quantumGeometryOp H x))
        (modularGeneratorGaugePart (E := E) hMod))
    (hCommGaugePhase :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod)) :
    ( deriv
        (fun t =>
          berryTwoFormJEpsOfOperator
            (E := E)
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).1)
            u v)
        0
    , deriv
        (fun t =>
          berryTwoFormJEpsOfOperator
            (E := E)
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).2)
            u v)
        0 )
      =
    ( berryTwoFormJEpsOfOperator
        (E := E)
        (relativeModularSourceDeriv (E := E) hMod
          (dualSheetLift (E := E) (quantumGeometryOp H x)))
        u v
    , berryTwoFormJEpsOfOperator
        (E := E)
        (relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
        u v ) := by
  apply Prod.ext
  · simpa [quantumGeometryEinsteinTransportedOperatorPair] using
      deriv_berryTwoFormJEpsOfOperator_modularTransport_conjugation_at_zero_eq_berryTwoFormJEpsOf_relativeModularSourceDeriv_of_commute_gaugePart
        (E := E) hMod (dualSheetLift (E := E) (quantumGeometryOp H x)) hCommGaugeMetric u v
  · simpa [quantumGeometryEinsteinTransportedOperatorPair] using
      deriv_berryTwoFormJEpsOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_berryTwoFormJEpsOf_relativeModularSourceDeriv_of_commute_gaugePart
        (E := E) CCI hMod hCommGaugePhase u v

/--
Generic same-state metric readout of an operator equals the owned
comparison-state generator metric against the identity channel.
-/
theorem metricOfOperator_self_eq_comparisonStateGeneratorMetric_id
    (A : EndH) (comparison : H₂) :
    metricOfOperator (E := E) A comparison comparison
      =
    comparisonStateGeneratorMetric (E := E) comparison
      A (ContinuousLinearMap.id ℝ H₂) := by
  simp [metricOfOperator_apply, comparisonStateGeneratorMetric_apply]

/--
Generic same-state Berry readout of an operator equals the owned
comparison-state phase form against the identity channel.
-/
theorem berryOfOperator_self_eq_comparisonStateGeneratorPhase_id
    (A : EndH) (comparison : H₂) :
    berryOfOperator (E := E) A comparison comparison
      =
    comparisonStateGeneratorPhase (E := E) comparison
      A (ContinuousLinearMap.id ℝ H₂) := by
  simp [berryOfOperator, metricOfOperator_apply, comparisonStateGeneratorPhase_apply]

/--
Same-state specialization of the transported operator pair:
under gauge commutation on both components, the infinitesimal transported
metric/phase readouts land directly on the owned comparison-state
metric/phase generator forms for the corresponding source derivatives.
-/
theorem deriv_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_comparisonStateGeneratorMetricPhase_source_pair_of_commute_gaugePart
    (H : HessianGeometry E) (x : E)
    (CCI : CertifiedConformalInference E) (hMod : EndH)
    (comparison : H₂)
    (hCommGaugeMetric :
      Commute
        (dualSheetLift (E := E) (quantumGeometryOp H x))
        (modularGeneratorGaugePart (E := E) hMod))
    (hCommGaugePhase :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod)) :
    ( deriv
        (fun t =>
          metricOfOperator
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).1)
            comparison comparison)
        0
    , deriv
        (fun t =>
          berryOfOperator
            (E := E)
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).2)
            comparison comparison)
        0 )
      =
    ( comparisonStateGeneratorMetric (E := E) comparison
        (relativeModularSourceDeriv (E := E) hMod
          (dualSheetLift (E := E) (quantumGeometryOp H x)))
        (ContinuousLinearMap.id ℝ H₂)
    , comparisonStateGeneratorPhase (E := E) comparison
        (relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
        (ContinuousLinearMap.id ℝ H₂) ) := by
  apply Prod.ext
  · exact
      (congrArg Prod.fst
        (deriv_metricOfOperator_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_metricOf_relativeModularSourceDeriv_pair_of_commute_gaugePart
          (E := E) (H := H) (x := x) (CCI := CCI) (hMod := hMod)
          (u := comparison) (v := comparison) hCommGaugeMetric hCommGaugePhase)).trans
        (metricOfOperator_self_eq_comparisonStateGeneratorMetric_id
          (E := E)
          (A := relativeModularSourceDeriv (E := E) hMod
            (dualSheetLift (E := E) (quantumGeometryOp H x)))
          (comparison := comparison))
  · exact
      (congrArg Prod.snd
        (deriv_berryOfOperator_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_berryOf_relativeModularSourceDeriv_pair_of_commute_gaugePart
          (E := E) (H := H) (x := x) (CCI := CCI) (hMod := hMod)
          (u := comparison) (v := comparison) hCommGaugeMetric hCommGaugePhase)).trans
        (berryOfOperator_self_eq_comparisonStateGeneratorPhase_id
          (E := E)
          (A := relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
          (comparison := comparison))

/--
State-dependent owner packaging of the dynamic operator pair in the general
noncommuting setting: the infinitesimal transported metric/phase readouts agree
with the `StateQGTReadout` owner surface for the constant modular datum and the
original operator seeds.
-/
theorem deriv_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_stateQGTReadout_constant_pair
    (H : HessianGeometry E) (x : E)
    (CCI : CertifiedConformalInference E) (hMod : EndH)
    (ψ u v : H₂) :
    ( deriv
        (fun t =>
          metricOfOperator
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).1)
            u v)
        0
    , deriv
        (fun t =>
          berryOfOperator
            (E := E)
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).2)
            u v)
        0 )
      =
    ( (stateQGTReadout (E := E)
          (constantStateModularDatum (E := E) hMod)
          ψ
          (dualSheetLift (E := E) (quantumGeometryOp H x))).metric
          u v
    , (stateQGTReadout (E := E)
          (constantStateModularDatum (E := E) hMod)
          ψ
          CCI.liftedEinsteinAnomalyOperator).phase
          u v ) := by
  apply Prod.ext
  · calc
      deriv
        (fun t =>
          metricOfOperator
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).1)
            u v)
        0
        =
      metricOfOperator
        (relativeModularDeriv (E := E) hMod
          (dualSheetLift (E := E) (quantumGeometryOp H x)))
        u v := by
          simpa [quantumGeometryEinsteinTransportedOperatorPair] using
            deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularDeriv
              (E := E) hMod (dualSheetLift (E := E) (quantumGeometryOp H x)) u v
      _ =
      (stateQGTReadout (E := E)
          (constantStateModularDatum (E := E) hMod)
          ψ
          (dualSheetLift (E := E) (quantumGeometryOp H x))).metric
        u v := by
          simpa using
            (congrArg Prod.fst
              (stateQGTReadout_constant_apply_eq_metricPhase_relativeModularDeriv
                (E := E) hMod
                (dualSheetLift (E := E) (quantumGeometryOp H x))
                ψ u v)).symm
  · calc
      deriv
        (fun t =>
          berryOfOperator
            (E := E)
            ((quantumGeometryEinsteinTransportedOperatorPair H x CCI hMod t).2)
            u v)
        0
        =
      berryOfOperator
        (E := E)
        (relativeModularDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
        u v := by
          simpa [quantumGeometryEinsteinTransportedOperatorPair, berryOfOperator] using
            deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_relativeModularDeriv
              (E := E) hMod CCI.liftedEinsteinAnomalyOperator u v
      _ =
      (stateQGTReadout (E := E)
          (constantStateModularDatum (E := E) hMod)
          ψ
          CCI.liftedEinsteinAnomalyOperator).phase
        u v := by
          simpa using
            (congrArg Prod.snd
              (stateQGTReadout_constant_apply_eq_metricPhase_relativeModularDeriv
                (E := E) hMod
                CCI.liftedEinsteinAnomalyOperator
                ψ u v)).symm

/--
The doubled quantum-geometry operator is read by the primitive two-state channel
correlation surface when paired with the identity channel.
-/
theorem metricOfOperator_dualSheetLift_quantumGeometryOp_eq_twoStateChannelCorrelation_id
    (H : HessianGeometry E) (x : E) (u v : H₂) :
    metricOfOperator
        (dualSheetLift (E := E) (quantumGeometryOp H x))
        u v
      =
    twoStateChannelCorrelation (E := E) u v
      (dualSheetLift (E := E) (quantumGeometryOp H x))
      (ContinuousLinearMap.id ℝ H₂) := by
  simp [metricOfOperator_apply, twoStateChannelCorrelation_apply]

/--
At the same doubled state, the doubled quantum-geometry operator is the metric
side of the primitive comparison-state generator form.
-/
theorem metricOfOperator_dualSheetLift_quantumGeometryOp_self_eq_comparisonStateGeneratorMetric
    (H : HessianGeometry E) (x : E) (comparison : H₂) :
    metricOfOperator
        (dualSheetLift (E := E) (quantumGeometryOp H x))
        comparison comparison
      =
    comparisonStateGeneratorMetric (E := E) comparison
      (dualSheetLift (E := E) (quantumGeometryOp H x))
      (ContinuousLinearMap.id ℝ H₂) := by
  rw [metricOfOperator_dualSheetLift_quantumGeometryOp_eq_twoStateChannelCorrelation_id
    (E := E) (H := H) (x := x) (u := comparison) (v := comparison)]
  exact comparisonGeneratorMetric_eq_twoStateChannelCorrelation_self
    (E := E) comparison
    (dualSheetLift (E := E) (quantumGeometryOp H x))
    (ContinuousLinearMap.id ℝ H₂)

/--
The doubled quantum-geometry metric readout and the welded projector-obstruction
phase readout land simultaneously on the owned comparison-state metric/phase
surfaces.
-/
theorem quantumGeometryMetric_and_weldedProjectorPhase_eq_comparisonMetricPhase
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E)
    (ψ comparison : H₂)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    ( metricOfOperator
        (dualSheetLift (E := E) (quantumGeometryOp H x))
        comparison comparison
    , weldedProjectorObstructionStatePhaseReadout (E := E) SCI ψ comparison comparison )
      =
    ( comparisonStateGeneratorMetric (E := E) comparison
        (dualSheetLift (E := E) (quantumGeometryOp H x))
        (ContinuousLinearMap.id ℝ H₂)
    , comparisonStateGeneratorPhase (E := E) comparison
        (liftedProjectorObstructionCorrelationSeed (E := E) SCI)
        (ContinuousLinearMap.id ℝ H₂) ) := by
  apply Prod.ext
  · exact metricOfOperator_dualSheetLift_quantumGeometryOp_self_eq_comparisonStateGeneratorMetric
      (E := E) (H := H) (x := x) (comparison := comparison)
  · exact weldedProjectorObstructionStatePhaseReadout_self_eq_comparisonStateGeneratorPhase
      (E := E) SCI ψ comparison hProj

/--
The transported antisymmetric projector-obstruction correlation is immediately
translated to the full operatorial second component of the static bridge pair.

This keeps the lower correlation representation as a translator surface only:
the target uses the operator carried by `quantumGeometryProjectorOperatorPair`
directly as the probe vector in the full comparison-metric readout.
-/
theorem deriv_comparisonTransportPhaseShiftedChannelCorrelation_liftedProjectorObstructionCorrelationSeed_at_zero_eq_comparisonMetricReadout_snd_quantumGeometryProjectorOperatorPair
    (H : HessianGeometry E) (x : E)
    (SCI : StarCertifiedConformalInference E)
    (R : InfoGeometry.Canonical.RelationalInformationCore.RelationalInformationDatum (E := E)) :
    deriv
      (fun t =>
        comparisonTransportPhaseShiftedChannelCorrelation (E := E) R
          (liftedProjectorObstructionCorrelationSeed (E := E) SCI)
          (ContinuousLinearMap.id ℝ H₂) t)
      0
      =
    (InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout R
      (ContinuousLinearMap.id ℝ H₂))
      R.comparisonState
      (((quantumGeometryProjectorOperatorPair (E := E) H x SCI).2)
        R.comparisonState) := by
  simpa [quantumGeometryProjectorOperatorPair] using
    deriv_comparisonTransportPhaseShiftedChannelCorrelation_liftedProjectorObstructionCorrelationSeed_at_zero_eq_comparisonMetricReadout
      (R := R) (SCI := SCI)

end InfoGeometry.Quantum
