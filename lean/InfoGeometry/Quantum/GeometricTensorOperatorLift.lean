import InfoGeometry.Quantum.GeometricTensor
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Canonical.BogoliubovTransport
import InfoGeometry.Canonical.EinsteinAnomalyOperator
import InfoGeometry.Krein.SplitQuadratic

open scoped InnerProductSpace

namespace InfoGeometry.Quantum

open InfoGeometry.Krein
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.ConformalUnification

namespace GeometricQuantumTensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Positive Cartan-side lift of a doubled-carrier operator to a bilinear form.
This is the Hilbert-side QGT seed associated to the local involution split.
-/
noncomputable def metricOfOperator (A : EndH) : LinearMap.BilinForm ℝ H₂ :=
  LinearMap.mk₂ ℝ
    (fun u v => ⟪A u, v⟫_ℝ)
    (by
      intro u₁ u₂ v
      simp [map_add, inner_add_left])
    (by
      intro c u v
      simp [map_smul, real_inner_smul_left, smul_eq_mul, mul_add])
    (by
      intro u v₁ v₂
      simp [inner_add_right])
    (by
      intro c u v
      simp [real_inner_smul_right, smul_eq_mul, mul_add])

omit [CompleteSpace E] in
@[simp] theorem metricOfOperator_apply
    (A : EndH) (u v : H₂) :
    metricOfOperator A u v = ⟪A u, v⟫_ℝ := rfl

omit [CompleteSpace E] in
@[simp] theorem metricOfOperator_zero :
    metricOfOperator (E := E) (0 : EndH) = 0 := by
  ext u v
  simp [metricOfOperator_apply]

omit [CompleteSpace E] in
@[simp] theorem metricOfOperator_add
    (A B : EndH) :
    metricOfOperator (E := E) (A + B)
      = metricOfOperator (E := E) A + metricOfOperator (E := E) B := by
  ext u v
  simp [metricOfOperator_apply, inner_add_left]

/--
Infinitesimal transport law for the operatorial metric seed under exponential
conjugation: the derivative at `t = 0` is the metric readout of the commutator.
-/
theorem hasDerivAt_metricOfOperator_expTransport_at_zero
    (X A : EndH) (u v : H₂) :
    HasDerivAt
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport (A := EndH) X A t) u v)
      (metricOfOperator (transportCommutator (E := E) X A) u v)
      0 := by
  let ω : EndH →L[ℝ] ℝ :=
    (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ H₂ u)
  have hω : HasDerivAt (fun _ : ℝ => ω) (0 : EndH →L[ℝ] ℝ) 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := ω))
  have hExp :
      HasDerivAt
        (fun t : ℝ => InfoGeometry.Canonical.expTransport (A := EndH) X A t)
        ⁅X, A⁆
        0 := by
    simpa using
      (InfoGeometry.Canonical.hasDerivAt_expTransport_at_zero (A := EndH) X A)
  have hApply :
      HasDerivAt
        (fun t : ℝ =>
          (fun _ : ℝ => ω) t
            (InfoGeometry.Canonical.expTransport (A := EndH) X A t))
        ((0 : EndH →L[ℝ] ℝ)
          (InfoGeometry.Canonical.expTransport (A := EndH) X A 0) + ω ⁅X, A⁆)
        0 :=
    hω.clm_apply hExp
  have hωEval :
      ω ⁅X, A⁆ = metricOfOperator (transportCommutator (E := E) X A) u v := by
    rw [← lieBracket_eq_transportCommutator (E := E) X A]
    simp [ω, metricOfOperator_apply, real_inner_comm]
  have hMain :
      HasDerivAt
        (fun t : ℝ =>
          metricOfOperator
            (InfoGeometry.Canonical.expTransport (A := EndH) X A t) u v)
        (ω ⁅X, A⁆)
        0 := by
    simpa [ω, metricOfOperator_apply, real_inner_comm] using hApply
  exact hωEval ▸ hMain

/--
Derivative form of `hasDerivAt_metricOfOperator_expTransport_at_zero`.
-/
theorem deriv_metricOfOperator_expTransport_at_zero
    (X A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport (A := EndH) X A t) u v)
      0
      =
    metricOfOperator (transportCommutator (E := E) X A) u v := by
  exact (hasDerivAt_metricOfOperator_expTransport_at_zero (E := E) X A u v).deriv

/--
Infinitesimal modular-conjugation transport law for the QGT operatorial metric
seed: derivative at `t = 0` equals the metric readout of the true modular
transport commutator.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator
      (transportCommutator (E := E) (modularTransportGenerator (E := E) hMod) A)
      u v := by
  simpa using
    deriv_metricOfOperator_expTransport_at_zero
      (E := E) (X := modularTransportGenerator (E := E) hMod) (A := A) u v

/--
Modular-derivation form of infinitesimal metric-seed transport at `t = 0`.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator (modularDeriv (E := E) hMod A) u v := by
  simpa [modularDeriv] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero (E := E) hMod A u v

/--
Relative-modular form: infinitesimal QGT metric-seed transport equals the metric
readout of the relative-modular derivation.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularDeriv
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator (relativeModularDeriv (E := E) hMod A) u v := by
  simpa [relativeModularKGenerator, relativeModularDeriv] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
      (E := E) hMod A u v

/--
The infinitesimal metric-seed transport splits into volume-preserving
(gauge/phase-linear) and dissipative (scaling/phase-antilinear) channels.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_split
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator
      (modularGaugeDeriv (E := E) hMod A)
      u v
      +
    metricOfOperator
      (modularScaleDeriv (E := E) hMod A)
      u v := by
  rw [deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
      (E := E) hMod A u v]
  rw [modularDeriv_split (E := E) hMod A]
  rw [metricOfOperator_add]
  simp

/--
Relative-modular form of the infinitesimal split:
gauge channel plus source channel.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularGaugeDeriv_add_metricOf_relativeModularSourceDeriv
    (hMod A : EndH) (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator
      (modularGaugeDeriv (E := E) hMod A)
      u v
      +
    metricOfOperator
      (relativeModularSourceDeriv (E := E) hMod A)
      u v := by
  simpa [relativeModularKGenerator, relativeModularSourceDeriv] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_split
      (E := E) hMod A u v

/--
If the transported operator commutes with the gauge sector of the modular
generator, the infinitesimal metric-seed transport is purely scaling.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularScaleDeriv_of_commute_gaugePart
    (hMod A : EndH)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator (modularScaleDeriv (E := E) hMod A) u v := by
  rw [deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
      (E := E) hMod A u v]
  rw [modularDeriv_eq_modularScaleDeriv_of_commute_gaugePart (E := E) hMod A hCommGauge]

/--
Relative-modular source-channel form:
if gauge commutes, the infinitesimal QGT metric-seed transport is purely source.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
    (hMod A : EndH)
    (hCommGauge : Commute A (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator (relativeModularSourceDeriv (E := E) hMod A) u v := by
  simpa [relativeModularKGenerator, relativeModularSourceDeriv] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularScaleDeriv_of_commute_gaugePart
      (E := E) hMod A hCommGauge u v

/--
For the certified doubled Einstein anomaly operator, gauge-sector commutation
forces the infinitesimal QGT transport entirely into the relative-modular
source channel.
-/
theorem deriv_metricOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
    (CCI : CertifiedConformalInference E)
    (hMod : EndH)
    (hCommGauge :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            CCI.liftedEinsteinAnomalyOperator
            t)
          u v)
      0
      =
    metricOfOperator
      (relativeModularSourceDeriv (E := E) hMod CCI.liftedEinsteinAnomalyOperator)
      u v := by
  exact
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) hMod CCI.liftedEinsteinAnomalyOperator hCommGauge u v

/--
Star-certified carrier form of the source-channel theorem:
for the lifted Einstein anomaly operator coming from a star-certified conformal
package, gauge-sector commutation forces infinitesimal QGT transport entirely
into the relative-modular source channel.
-/
theorem deriv_metricOfOperator_starCertified_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
    (SCI : StarCertifiedConformalInference E)
    (hMod : EndH)
    (hCommGauge :
      Commute SCI.liftedEinsteinAnomalyOperator
        (modularGeneratorGaugePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            SCI.liftedEinsteinAnomalyOperator
            t)
          u v)
      0
      =
    metricOfOperator
      (relativeModularSourceDeriv (E := E) hMod SCI.liftedEinsteinAnomalyOperator)
      u v := by
  simpa [StarCertifiedConformalInference.liftedEinsteinAnomalyOperator] using
    deriv_metricOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart
      (E := E) SCI.toCertifiedConformalInference hMod hCommGauge u v

/--
If the transported operator commutes with the scaling sector of the modular
generator, the infinitesimal metric-seed transport is purely gauge.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularGaugeDeriv_of_commute_scalePart
    (hMod A : EndH)
    (hCommScale : Commute A (modularGeneratorScalePart (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    metricOfOperator (modularGaugeDeriv (E := E) hMod A) u v := by
  rw [deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
      (E := E) hMod A u v]
  rw [modularDeriv_eq_modularGaugeDeriv_of_commute_scalePart (E := E) hMod A hCommScale]

/--
If the transported operator commutes with the true modular transport generator,
the infinitesimal metric-seed transport vanishes at `t = 0`.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_of_commute
    (hMod A : EndH)
    (hComm : Commute A (modularTransportGenerator (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (modularTransportGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    0 := by
  rw [deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv
      (E := E) hMod A u v]
  rw [modularDeriv_eq_zero_of_commute_generator (E := E) hMod A hComm]
  rw [metricOfOperator_zero]
  rfl

/--
Relative-modular commuting-sector stationarity:
if `A` commutes with the relative-modular `K`-generator, the infinitesimal QGT
metric-seed transport vanishes.
-/
theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_of_commute_relativeModularKGenerator
    (hMod A : EndH)
    (hComm : Commute A (relativeModularKGenerator (E := E) hMod))
    (u v : H₂) :
    deriv
      (fun t =>
        metricOfOperator
          (InfoGeometry.Canonical.expTransport
            (A := EndH)
            (relativeModularKGenerator (E := E) hMod)
            A
            t)
          u v)
      0
      =
    0 := by
  simpa [relativeModularKGenerator] using
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_of_commute
      (E := E) hMod A hComm u v


/-- A Hilbert-self-adjoint seed induces a symmetric metric on the doubled carrier. -/
theorem metricOfOperator_isSymm_of_selfAdjoint
    (A : EndH)
    (hA : IsSelfAdjoint A) :
    (metricOfOperator A).IsSymm := by
  refine ⟨?_⟩
  intro u v
  calc
    metricOfOperator A u v = ⟪A u, v⟫_ℝ := rfl
    _ = ⟪u, A.adjoint v⟫_ℝ := by rw [ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪u, A v⟫_ℝ := by rw [IsSelfAdjoint.adjoint_eq hA]
    _ = ⟪A v, u⟫_ℝ := by rw [real_inner_comm]
    _ = metricOfOperator A v u := rfl

/--
If `A` commutes with the local Cartan phase axis `K = Jε`, then the induced
metric satisfies the exact `K`-skew law required by `QGT.ofMajorana`.
-/
theorem metricOfOperator_K_skew_of_commutesWithK
    (A : EndH)
    (hComm :
      A.comp (modularComplexI (E := E))
        =
      (modularComplexI (E := E)).comp A) :
    ∀ u v,
      metricOfOperator A (modularComplexI (E := E) u) v
        =
      -metricOfOperator A u (modularComplexI (E := E) v) := by
  intro u v
  have hCommEval : A (modularComplexI (E := E) u) = modularComplexI (E := E) (A u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hComm
  rw [metricOfOperator_apply, metricOfOperator_apply, hCommEval]
  exact modularComplexI_inner_skew (E := E) (A u) v

/--
Operatorial lift of the doubled real QGT from a Hilbert-self-adjoint operator
commuting with the local Cartan phase axis `K = Jε`.
-/
noncomputable def qgtOfOperator
    (A : EndH)
    (hA : IsSelfAdjoint A)
    (hComm :
      A.comp (modularComplexI (E := E))
        =
      (modularComplexI (E := E)).comp A) : QGT E :=
  ofMajorana
    (metricOfOperator A)
    (metricOfOperator_isSymm_of_selfAdjoint (A := A) hA)
    (metricOfOperator_K_skew_of_commutesWithK (E := E) (A := A) hComm)

/--
Krein-side lift of a doubled-carrier operator to a bilinear form.
This is the indefinite-metric seed on the Cartan-odd branch.
-/
noncomputable def kreinMetricOfOperator (A : EndH) : LinearMap.BilinForm ℝ H₂ :=
  (KreinSpace.kreinBilin (H := H₂)).compLeft A.toLinearMap

@[simp] theorem kreinMetricOfOperator_apply
    (A : EndH) (u v : H₂) :
    kreinMetricOfOperator A u v = KreinSpace.kreinInner (H := H₂) (A u) v := rfl

/-- A Krein-self-adjoint seed induces a symmetric Krein-side metric on the doubled carrier. -/
theorem kreinMetricOfOperator_isSymm_of_kreinSelfAdjoint
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A) :
    (kreinMetricOfOperator A).IsSymm := by
  refine ⟨?_⟩
  intro u v
  rw [kreinMetricOfOperator_apply, kreinMetricOfOperator_apply,
    KreinSpace.kreinInner_kreinAdjoint, hA]
  exact KreinSpace.kreinInner_symm (H := H₂) u (A v)

/--
If `A` lies in the Cartan-odd / phase-antilinear branch relative to `K = Jε`,
then the induced Krein metric satisfies the exact `K`-skew law required by
`QGT.ofMajorana`.
-/
theorem kreinMetricOfOperator_K_skew_of_IsPhaseAntilinear
    (A : EndH)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    ∀ u v,
      kreinMetricOfOperator A (modularComplexI (E := E) u) v
        =
      -kreinMetricOfOperator A u (modularComplexI (E := E) v) := by
  intro u v
  have hAntiEval :
      A (modularComplexI (E := E) u)
        =
      -((modularComplexI (E := E)) (A u)) := by
    have h := congrArg (fun T : EndH => T u) hAnti
    simpa [IsPhaseAntilinear, ContinuousLinearMap.comp_apply] using h
  rw [kreinMetricOfOperator_apply, kreinMetricOfOperator_apply, hAntiEval]
  calc
    KreinSpace.kreinInner (H := H₂) (-((modularComplexI (E := E)) (A u))) v
      = -KreinSpace.kreinInner (H := H₂) ((modularComplexI (E := E)) (A u)) v := by
          simp
    _ = -KreinSpace.kreinInner (H := H₂) (A u) ((modularComplexI (E := E)) v) := by
          rw [modularComplexI_kreinInner_swap]
    _ = -kreinMetricOfOperator A u (modularComplexI (E := E) v) := by
          rw [kreinMetricOfOperator_apply]

/--
The Krein-side operator metric is exactly the Hilbert-side operator metric after
transporting the seed by the doubled fundamental symmetry `ε`.
-/
theorem metricOfOperator_modularSignEpsilon_comp_eq_kreinMetricOfOperator
    (A : EndH) :
    metricOfOperator ((modularSignEpsilon (E := E)).comp A)
      =
    kreinMetricOfOperator A := by
  ext u v
  rw [metricOfOperator_apply, kreinMetricOfOperator_apply, krein_inner_prod_l2]
  simp [modularSignEpsilon, spectral_epsilon, WithLp.prod_inner_apply, sub_eq_add_neg]

@[simp] theorem inner_modularSignEpsilon_apply_eq_kreinInner
    (u v : H₂) :
    ⟪(modularSignEpsilon (E := E)) u, v⟫_ℝ
      =
    KreinSpace.kreinInner (H := H₂) u v := by
  rw [krein_inner_prod_l2]
  simp [modularSignEpsilon, spectral_epsilon, WithLp.prod_inner_apply, sub_eq_add_neg]

@[simp] theorem inner_apply_modularSignEpsilon_eq_kreinInner
    (u v : H₂) :
    ⟪u, (modularSignEpsilon (E := E)) v⟫_ℝ
      =
    KreinSpace.kreinInner (H := H₂) u v := by
  calc
    ⟪u, (modularSignEpsilon (E := E)) v⟫_ℝ
      =
    ⟪(modularSignEpsilon (E := E)) u, v⟫_ℝ := by
          rw [modularSignEpsilon]
          rw [InfoGeometry.Krein.SplitQuadratic.spectral_epsilon_selfAdj (E := E) u v]
    _ = KreinSpace.kreinInner (H := H₂) u v := by
          simpa using inner_modularSignEpsilon_apply_eq_kreinInner (E := E) u v

/--
Modular-centered operator seed whose diagonal metric readout is the modular
variance.

This is the `ε`-transported square of the centered modular generator, so it
lands on the Hilbert-side operator lift while preserving the Krein variance
content on the state slice.
-/
noncomputable def modularVarianceSeed
    (ψ : H₂) (hMod : EndH) : EndH :=
  (modularSignEpsilon (E := E)).comp
    ((centeredModularGenerator (E := E) ψ hMod)
      * (centeredModularGenerator (E := E) ψ hMod))

/-- The modular-variance seed has exactly the modular variance on the diagonal metric slice. -/
theorem metricOfOperator_modularVarianceSeed_diag_eq_modularVariance
    (ψ : H₂) (hMod : EndH) :
    metricOfOperator (E := E) (modularVarianceSeed (E := E) ψ hMod) ψ ψ
      = modularVariance (E := E) ψ hMod := by
  let B : EndH :=
    (centeredModularGenerator (E := E) ψ hMod)
      * (centeredModularGenerator (E := E) ψ hMod)
  calc
    metricOfOperator (E := E) (modularVarianceSeed (E := E) ψ hMod) ψ ψ
        = ⟪(modularSignEpsilon (E := E)) (B ψ), ψ⟫_ℝ := by
            simp [metricOfOperator_apply, modularVarianceSeed, B, ContinuousLinearMap.comp_apply]
    _ = KreinSpace.kreinInner (H := H₂) (B ψ) ψ := by
          simpa using inner_modularSignEpsilon_apply_eq_kreinInner (E := E) (B ψ) ψ
    _ = KreinSpace.kreinInner (H := H₂) ψ (B ψ) := by
          simpa using (KreinSpace.kreinInner_symm (H := H₂) (B ψ) ψ)
    _ = modularVariance (E := E) ψ hMod := by
          simp [modularVariance, kreinExpectation, B]

/-- Main owner predicate: the QGT metric on a chosen state slice realizes modular variance. -/
def QGTRealizesModularVariance
    (Q : GeometricQuantumTensor E) (ψ : H₂) (hMod : EndH) : Prop :=
  Q.metric ψ ψ = modularVariance (E := E) ψ hMod

/--
Owner theorem: once the modular-variance seed is admitted by the Hilbert-side
QGT lift (`selfAdjoint` + Cartan-even commutation), the lifted QGT metric
realizes modular variance on the chosen state slice.
-/
theorem qgtOfOperator_modularVarianceSeed_realizes_modularVariance
    (ψ : H₂) (hMod : EndH)
    (hA : IsSelfAdjoint (modularVarianceSeed (E := E) ψ hMod))
    (hComm :
      (modularVarianceSeed (E := E) ψ hMod).comp (modularComplexI (E := E))
        =
      (modularComplexI (E := E)).comp (modularVarianceSeed (E := E) ψ hMod)) :
    QGTRealizesModularVariance (E := E)
      (qgtOfOperator (E := E) (modularVarianceSeed (E := E) ψ hMod) hA hComm)
      ψ hMod := by
  exact metricOfOperator_modularVarianceSeed_diag_eq_modularVariance
    (E := E) ψ hMod

/--
Transport by the doubled fundamental symmetry `ε` sends a Krein-self-adjoint
seed to a Hilbert-self-adjoint seed.
-/
theorem isSelfAdjoint_modularSignEpsilon_comp_of_kreinSelfAdjoint
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A) :
    IsSelfAdjoint ((modularSignEpsilon (E := E)).comp A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  calc
    ⟪((modularSignEpsilon (E := E)).comp A) u, v⟫_ℝ
        = KreinSpace.kreinInner (H := H₂) (A u) v := by
            simpa [ContinuousLinearMap.comp_apply] using
              (inner_modularSignEpsilon_apply_eq_kreinInner (E := E) (A u) v)
    _ = KreinSpace.kreinInner (H := H₂) u (A v) := by
          rw [KreinSpace.kreinInner_kreinAdjoint, hA]
    _ = ⟪u, ((modularSignEpsilon (E := E)).comp A) v⟫_ℝ := by
          simpa [ContinuousLinearMap.comp_apply] using
            (inner_apply_modularSignEpsilon_eq_kreinInner (E := E) u (A v)).symm

/--
Transport by the doubled fundamental symmetry `ε` sends the Cartan-odd /
phase-antilinear branch to the phase-linear branch.
-/
theorem isPhaseLinear_modularSignEpsilon_comp_of_IsPhaseAntilinear
    (A : EndH)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    IsPhaseLinear (E := E) ((modularSignEpsilon (E := E)).comp A) := by
  have hEpsK :
      (modularSignEpsilon (E := E)).comp (modularComplexI (E := E))
        =
      -(modularConjugationJ (E := E)) := by
    simpa [modularConjugationJ, modularSignEpsilon, modularComplexI] using
      (InfoGeometry.Krein.spectral_epsilon_comp_complex_i (E := E))
  have hKEps :
      (modularComplexI (E := E)).comp (modularSignEpsilon (E := E))
        =
      modularConjugationJ (E := E) := by
    simpa [modularConjugationJ, modularSignEpsilon, modularComplexI] using
      (InfoGeometry.Krein.complex_i_comp_spectral_epsilon (E := E))
  unfold IsPhaseLinear IsPhaseAntilinear at *
  calc
    (((modularSignEpsilon (E := E)).comp A).comp (modularComplexI (E := E)))
        = (modularSignEpsilon (E := E)).comp (A.comp (modularComplexI (E := E))) := by
            simp [ContinuousLinearMap.comp_assoc]
    _ = (modularSignEpsilon (E := E)).comp (-((modularComplexI (E := E)).comp A)) := by
          rw [hAnti]
    _ = -(((modularSignEpsilon (E := E)).comp (modularComplexI (E := E))).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = -((-(modularConjugationJ (E := E))).comp A) := by rw [hEpsK]
    _ = (modularConjugationJ (E := E)).comp A := by
          simp
    _ = ((modularComplexI (E := E)).comp (modularSignEpsilon (E := E))).comp A := by rw [hKEps]
    _ = (modularComplexI (E := E)).comp ((modularSignEpsilon (E := E)).comp A) := by
          simp [ContinuousLinearMap.comp_assoc]

/--
Operatorial lift of the doubled real QGT from a Krein-self-adjoint operator in
the Cartan-odd / phase-antilinear branch of the local `K`-involution.
-/
noncomputable def kreinQgtOfOperator
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A) : QGT E :=
  ofMajorana
    (kreinMetricOfOperator A)
    (kreinMetricOfOperator_isSymm_of_kreinSelfAdjoint (A := A) hA)
    (kreinMetricOfOperator_K_skew_of_IsPhaseAntilinear (E := E) (A := A) hAnti)

/--
The Hilbert-side and Krein-side QGT lifts agree on the metric after transport
by the doubled fundamental symmetry `ε`.
-/
theorem qgtOfOperator_modularSignEpsilon_comp_metric_eq_kreinQgtOfOperator_metric
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    (qgtOfOperator
        (E := E)
        ((modularSignEpsilon (E := E)).comp A)
        (isSelfAdjoint_modularSignEpsilon_comp_of_kreinSelfAdjoint
          (E := E) (A := A) hA)
        (isPhaseLinear_modularSignEpsilon_comp_of_IsPhaseAntilinear
          (E := E) (A := A) hAnti)).metric
      =
    (kreinQgtOfOperator (E := E) A hA hAnti).metric := by
  simp [qgtOfOperator, kreinQgtOfOperator,
    GeometricQuantumTensor.ofMajorana,
    metricOfOperator_modularSignEpsilon_comp_eq_kreinMetricOfOperator]

/--
The Hilbert-side and Krein-side QGT lifts agree on the Berry form after
transport by the doubled fundamental symmetry `ε`.
-/
theorem qgtOfOperator_modularSignEpsilon_comp_berry_eq_kreinQgtOfOperator_berry
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A) :
    (qgtOfOperator
        (E := E)
        ((modularSignEpsilon (E := E)).comp A)
        (isSelfAdjoint_modularSignEpsilon_comp_of_kreinSelfAdjoint
          (E := E) (A := A) hA)
        (isPhaseLinear_modularSignEpsilon_comp_of_IsPhaseAntilinear
          (E := E) (A := A) hAnti)).berry
      =
    (kreinQgtOfOperator (E := E) A hA hAnti).berry := by
  simp [qgtOfOperator, kreinQgtOfOperator,
    GeometricQuantumTensor.ofMajorana,
    metricOfOperator_modularSignEpsilon_comp_eq_kreinMetricOfOperator]

end GeometricQuantumTensor

end InfoGeometry.Quantum
