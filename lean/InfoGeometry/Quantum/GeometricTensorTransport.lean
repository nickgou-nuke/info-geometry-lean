import InfoGeometry.Quantum.GeometricTensorOperatorLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BogoliubovClosedForms
import InfoGeometry.Canonical.TomitaTakesaki

open scoped InnerProductSpace

namespace InfoGeometry.Quantum

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms
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
The exact local Cartan propagator `KRotation = exp(tK)` preserves the positive
doubled-space Hilbert metric.
-/
theorem KRotation_preserves_inner
    (t : ℝ) (u v : H₂) :
    ⟪KRotation (E := E) t u, KRotation (E := E) t v⟫_ℝ = ⟪u, v⟫_ℝ := by
  rw [KRotation_apply (E := E), KRotation_apply (E := E)]
  repeat rw [inner_add_left, inner_add_right]
  repeat rw [real_inner_smul_left, real_inner_smul_right]
  rw [inner_add_right]
  repeat rw [real_inner_smul_left, real_inner_smul_right]
  have hClockSkew :
      ⟪clockAxis (E := E) u, v⟫_ℝ = -⟪u, clockAxis (E := E) v⟫_ℝ := by
    exact InfoGeometry.Canonical.TomitaTakesaki.complex_i_inner_skew (E := E) u v
  have hClockComp :
      ⟪clockAxis (E := E) u, clockAxis (E := E) v⟫_ℝ = ⟪u, v⟫_ℝ := by
    exact InfoGeometry.Canonical.TomitaTakesaki.complex_i_inner_comp (E := E) u v
  rw [hClockSkew, hClockComp]
  ring_nf
  have hcossin : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  let g : ℝ := ⟪u, v⟫_ℝ
  change Real.cos t ^ 2 * g + g * Real.sin t ^ 2 = g
  calc
    Real.cos t ^ 2 * g + g * Real.sin t ^ 2 = g * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
    _ = g := by rw [hcossin]; ring

theorem KRotation_preserves_inner_complex_i
    (t : ℝ) (u v : H₂) :
    ⟪KRotation (E := E) t u, KRotation (E := E) t v⟫_ℝ = ⟪u, v⟫_ℝ := by
  exact KRotation_preserves_inner (E := E) t u v

/--
Infinitesimal modular-conjugation transport law for the operatorial QGT metric
seed in the commuting sector: the derivative at `t = 0` vanishes.
-/
theorem metricOfOperator_modularTransport_infinitesimal_stationary_of_commute_generator
    (A hMod : EndH)
    (hCommGen : Commute A (modularTransportGenerator (E := E) hMod))
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
  exact
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_of_commute
      (E := E) hMod A hCommGen u v

/--
If the transported operator commutes with the gauge sector of the modular
generator, the infinitesimal QGT metric transport is entirely carried by the
scaling channel.
-/
theorem metricOfOperator_modularTransport_infinitesimal_eq_scale_channel_of_commute_gaugePart
    (A hMod : EndH)
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
  exact
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularScaleDeriv_of_commute_gaugePart
      (E := E) hMod A hCommGauge u v

/--
If the transported operator commutes with the scaling sector of the modular
generator, the infinitesimal QGT metric transport is entirely carried by the
gauge channel.
-/
theorem metricOfOperator_modularTransport_infinitesimal_eq_gauge_channel_of_commute_scalePart
    (A hMod : EndH)
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
  exact
    deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularGaugeDeriv_of_commute_scalePart
      (E := E) hMod A hCommScale u v

/--
The operatorial metric seed carried by a Cartan-even operator commuting with
`K` is invariant under the exact phase propagator `exp(tK)`.
-/
theorem metricOfOperator_KRotation_eq_of_commute
    (A : EndH)
    (hComm :
      A.comp (clockAxis (E := E))
        =
      (clockAxis (E := E)).comp A)
    (t : ℝ) :
    ∀ u v : H₂,
      metricOfOperator A
          (KRotation (E := E) t u)
          (KRotation (E := E) t v)
        =
      metricOfOperator A u v := by
  intro u v
  have hIntertwine :
      A.comp (KRotation (E := E) t) = (KRotation (E := E) t).comp A :=
    comp_KRotation_eq_KRotation_comp_of_IsPhaseLinear
      (E := E) (A := A) hComm t
  have hEval : A (KRotation (E := E) t u) = KRotation (E := E) t (A u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hIntertwine
  rw [metricOfOperator_apply, hEval, metricOfOperator_apply]
  exact KRotation_preserves_inner (E := E) t (A u) v

/--
The operatorial Berry 2-form seed is preserved by the exact phase propagator
`KRotation = exp(tK)` whenever the seed commutes with `K = Jε`.
-/
theorem berryOfOperator_KRotation_eq_of_commute
    (A : EndH)
    (hComm :
      A.comp (clockAxis (E := E))
        =
      (clockAxis (E := E)).comp A)
    (t : ℝ) :
    ∀ u v : H₂,
      berryOfOperator (E := E) A
          (KRotation (E := E) t u)
          (KRotation (E := E) t v)
        =
      berryOfOperator (E := E) A u v := by
  intro u v
  have hKComm :
      (clockAxis (E := E)).comp (KRotation (E := E) t)
        =
      (KRotation (E := E) t).comp (clockAxis (E := E)) := by
    exact comp_KRotation_eq_KRotation_comp_of_IsPhaseLinear
      (E := E)
      (A := clockAxis (E := E))
      (by simp [IsPhaseLinear])
      t
  have hKu :
      clockAxis (E := E) (KRotation (E := E) t u)
        =
      KRotation (E := E) t (clockAxis (E := E) u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hKComm
  calc
    berryOfOperator (E := E) A
        (KRotation (E := E) t u)
        (KRotation (E := E) t v)
      =
    metricOfOperator (E := E) A
      (clockAxis (E := E) (KRotation (E := E) t u))
      (KRotation (E := E) t v) := by
          simpa using
            (berryOfOperator_apply (E := E) A
              (KRotation (E := E) t u)
              (KRotation (E := E) t v))
    _ =
    metricOfOperator (E := E) A
      (KRotation (E := E) t (clockAxis (E := E) u))
      (KRotation (E := E) t v) := by
          rw [hKu]
    _ = metricOfOperator (E := E) A (clockAxis (E := E) u) v := by
          exact metricOfOperator_KRotation_eq_of_commute
            (E := E) (A := A) hComm t (clockAxis (E := E) u) v
    _ = berryOfOperator (E := E) A u v := by
          exact (berryOfOperator_apply (E := E) A u v).symm

/--
Split-`Cl(1,1)` (`J ∘ ε`) form of the phase-propagation invariance theorem for
the operatorial Berry 2-form.
-/
theorem berryTwoFormJEpsOfOperator_KRotation_eq_of_commute
    (A : EndH)
    (hComm :
      A.comp (clockAxis (E := E))
        =
      (clockAxis (E := E)).comp A)
    (t : ℝ) :
    ∀ u v : H₂,
      berryTwoFormJEpsOfOperator (E := E) A
          (KRotation (E := E) t u)
          (KRotation (E := E) t v)
        =
      berryTwoFormJEpsOfOperator (E := E) A u v := by
  intro u v
  simpa [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E) A] using
    berryOfOperator_KRotation_eq_of_commute (E := E) (A := A) hComm t u v

/--
The operatorial QGT built from a self-adjoint Cartan-even seed is preserved by
the exact phase propagator `KRotation = exp(tK)`.
-/
theorem qgtOfOperator_KRotation_invariant
    (A : EndH)
    (hA : IsSelfAdjoint A)
    (hComm :
      A.comp (clockAxis (E := E))
        =
      (clockAxis (E := E)).comp A)
    (t : ℝ) :
    let Q := qgtOfOperator (E := E) A hA hComm
    (∀ u v : H₂,
      Q.metric (KRotation (E := E) t u) (KRotation (E := E) t v) = Q.metric u v)
      ∧
    (∀ u v : H₂,
      Q.berry (KRotation (E := E) t u) (KRotation (E := E) t v) = Q.berry u v) := by
  intro Q
  refine ⟨?_, ?_⟩
  · intro u v
    exact metricOfOperator_KRotation_eq_of_commute
      (E := E) (A := A) hComm t u v
  · intro u v
    have hMetric :
        ∀ x y : H₂,
          Q.metric (KRotation (E := E) t x) (KRotation (E := E) t y) = Q.metric x y :=
      metricOfOperator_KRotation_eq_of_commute
        (E := E) (A := A) hComm t
    have hKComm :
        (clockAxis (E := E)).comp (KRotation (E := E) t)
          =
        (KRotation (E := E) t).comp (clockAxis (E := E)) := by
      exact comp_KRotation_eq_KRotation_comp_of_IsPhaseLinear
        (E := E)
        (A := clockAxis (E := E))
        (by simp [IsPhaseLinear])
        t
    have hKu :
        clockAxis (E := E) (KRotation (E := E) t u)
          =
        KRotation (E := E) t (clockAxis (E := E) u) := by
      simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hKComm
    calc
      Q.berry (KRotation (E := E) t u) (KRotation (E := E) t v)
        =
      Q.metric ((clockAxis (E := E)) (KRotation (E := E) t u)) (KRotation (E := E) t v) := by
            exact Q.compat _ _
      _ =
      Q.metric ((KRotation (E := E) t) ((clockAxis (E := E)) u)) (KRotation (E := E) t v) := by
            rw [hKu]
      _ = Q.metric ((clockAxis (E := E)) u) v := hMetric _ _
      _ = Q.berry u v := (Q.compat u v).symm

/--
The operatorial metric seed is preserved along the exact modular transport flow
whenever the transported operator commutes with the true Cartan generator
`hMod ∘ K` and the seed `hMod` is phase-linear/self-adjoint.
-/
theorem metricOfOperator_modularTransportFlow_eq_of_commute_generator
    (A hMod : EndH)
    (hSelf : IsSelfAdjoint hMod)
    (hPhase : IsPhaseLinear (E := E) hMod)
    (hCommGen : Commute A (modularTransportGenerator (E := E) hMod))
    (t : ℝ) :
    ∀ u v : H₂,
      metricOfOperator A
          (modularTransportFlow (E := E) hMod t u)
          (modularTransportFlow (E := E) hMod t v)
        =
      metricOfOperator A u v := by
  intro u v
  have hIntertwine :
      A.comp (modularTransportFlow (E := E) hMod t)
        =
      (modularTransportFlow (E := E) hMod t).comp A := by
    have hCommScaled :
        Commute A (t • modularTransportGenerator (E := E) hMod) := by
      change
        A.comp (t • modularTransportGenerator (E := E) hMod)
          =
        (t • modularTransportGenerator (E := E) hMod).comp A
      simpa [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp] using
        congrArg (fun T : EndH => t • T) hCommGen.eq
    exact (show Commute A (modularTransportFlow (E := E) hMod t) from
      by simpa [modularTransportFlow] using hCommScaled.exp_right).eq
  have hEval :
      A (modularTransportFlow (E := E) hMod t u)
        =
      modularTransportFlow (E := E) hMod t (A u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hIntertwine
  rw [metricOfOperator_apply, hEval, metricOfOperator_apply]
  exact modularTransportFlow_preserves_inner_of_isSelfAdjoint_of_IsPhaseLinear
    (E := E) hMod hSelf hPhase t (A u) v

/--
Exact modular-flow transport of the operatorial Berry 2-form seed.

If `A` commutes with the true modular transport generator `hMod ∘ K`, then the
Berry seed is preserved along the full exponential Bogoliubov flow.
-/
theorem berryOfOperator_modularTransportFlow_eq_of_commute_generator
    (A hMod : EndH)
    (hSelf : IsSelfAdjoint hMod)
    (hPhase : IsPhaseLinear (E := E) hMod)
    (hCommGen : Commute A (modularTransportGenerator (E := E) hMod))
    (t : ℝ) :
    ∀ u v : H₂,
      berryOfOperator (E := E) A
          (modularTransportFlow (E := E) hMod t u)
          (modularTransportFlow (E := E) hMod t v)
        =
      berryOfOperator (E := E) A u v := by
  intro u v
  have hKComm :
      (clockAxis (E := E)).comp (modularTransportFlow (E := E) hMod t)
        =
      (modularTransportFlow (E := E) hMod t).comp (clockAxis (E := E)) := by
    exact
      modularComplexI_comp_modularTransportFlow_eq_modularTransportFlow_comp_modularComplexI_of_IsPhaseLinear
        (E := E) hMod hPhase t
  have hKu :
      clockAxis (E := E) (modularTransportFlow (E := E) hMod t u)
        =
      modularTransportFlow (E := E) hMod t (clockAxis (E := E) u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hKComm
  calc
    berryOfOperator (E := E) A
        (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v)
      =
    metricOfOperator (E := E) A
      (clockAxis (E := E) (modularTransportFlow (E := E) hMod t u))
      (modularTransportFlow (E := E) hMod t v) := by
          simp [berryOfOperator_apply]
    _ =
    metricOfOperator (E := E) A
      (modularTransportFlow (E := E) hMod t (clockAxis (E := E) u))
      (modularTransportFlow (E := E) hMod t v) := by
          rw [hKu]
    _ = metricOfOperator (E := E) A (clockAxis (E := E) u) v := by
          exact metricOfOperator_modularTransportFlow_eq_of_commute_generator
            (E := E) (A := A) (hMod := hMod) hSelf hPhase hCommGen t
            (clockAxis (E := E) u) v
    _ = berryOfOperator (E := E) A u v := by
          simp [berryOfOperator_apply]

/--
Split-`Cl(1,1)` (`J ∘ ε`) form of exact modular-flow Berry transport:
preservation along the exponential Bogoliubov flow in the commuting sector.
-/
theorem berryTwoFormJEpsOfOperator_modularTransportFlow_eq_of_commute_generator
    (A hMod : EndH)
    (hSelf : IsSelfAdjoint hMod)
    (hPhase : IsPhaseLinear (E := E) hMod)
    (hCommGen : Commute A (modularTransportGenerator (E := E) hMod))
    (t : ℝ) :
    ∀ u v : H₂,
      berryTwoFormJEpsOfOperator (E := E) A
          (modularTransportFlow (E := E) hMod t u)
          (modularTransportFlow (E := E) hMod t v)
        =
      berryTwoFormJEpsOfOperator (E := E) A u v := by
  intro u v
  simpa [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E) A] using
    berryOfOperator_modularTransportFlow_eq_of_commute_generator
      (E := E) (A := A) (hMod := hMod) hSelf hPhase hCommGen t u v

/--
Exact modular-flow transport of the certified lifted Einstein anomaly operator.

If the lifted Einstein anomaly commutes with the true modular transport
generator, then its operatorial metric seed is preserved along the full flow.
-/
theorem metricOfOperator_liftedEinsteinAnomalyOperator_modularTransportFlow_eq_of_commute_generator
    (CCI : CertifiedConformalInference E)
    (hMod : EndH)
    (hSelf : IsSelfAdjoint hMod)
    (hPhase : IsPhaseLinear (E := E) hMod)
    (hCommGen :
      Commute CCI.liftedEinsteinAnomalyOperator
        (modularTransportGenerator (E := E) hMod))
    (t : ℝ) :
    ∀ u v : H₂,
      metricOfOperator CCI.liftedEinsteinAnomalyOperator
          (modularTransportFlow (E := E) hMod t u)
          (modularTransportFlow (E := E) hMod t v)
        =
      metricOfOperator CCI.liftedEinsteinAnomalyOperator u v := by
  exact metricOfOperator_modularTransportFlow_eq_of_commute_generator
    (E := E) (A := CCI.liftedEinsteinAnomalyOperator) (hMod := hMod)
    hSelf hPhase hCommGen t

/--
The operatorial QGT is preserved along the exact modular transport flow in the
full Cartan-even commuting sector.
-/
theorem qgtOfOperator_modularTransportFlow_invariant_of_commute_generator
    (A hMod : EndH)
    (hA : IsSelfAdjoint A)
    (hACommK :
      A.comp (clockAxis (E := E))
        =
      (clockAxis (E := E)).comp A)
    (hSelf : IsSelfAdjoint hMod)
    (hPhase : IsPhaseLinear (E := E) hMod)
    (hCommGen : Commute A (modularTransportGenerator (E := E) hMod))
    (t : ℝ) :
    let Q := qgtOfOperator (E := E) A hA hACommK
    (∀ u v : H₂,
      Q.metric (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.metric u v)
      ∧
    (∀ u v : H₂,
      Q.berry (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.berry u v) := by
  intro Q
  refine ⟨?_, ?_⟩
  · intro u v
    exact metricOfOperator_modularTransportFlow_eq_of_commute_generator
      (E := E) (A := A) (hMod := hMod) hSelf hPhase hCommGen t u v
  · intro u v
    have hMetric :
        ∀ x y : H₂,
          Q.metric (modularTransportFlow (E := E) hMod t x)
            (modularTransportFlow (E := E) hMod t y) = Q.metric x y :=
      metricOfOperator_modularTransportFlow_eq_of_commute_generator
        (E := E) (A := A) (hMod := hMod) hSelf hPhase hCommGen t
    have hKComm :
        (clockAxis (E := E)).comp (modularTransportFlow (E := E) hMod t)
          =
        (modularTransportFlow (E := E) hMod t).comp (clockAxis (E := E)) := by
      exact modularComplexI_comp_modularTransportFlow_eq_modularTransportFlow_comp_modularComplexI_of_IsPhaseLinear
        (E := E) hMod hPhase t
    have hKu :
        clockAxis (E := E) (modularTransportFlow (E := E) hMod t u)
          =
        modularTransportFlow (E := E) hMod t (clockAxis (E := E) u) := by
      simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hKComm
    calc
      Q.berry (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v)
        =
      Q.metric ((clockAxis (E := E)) (modularTransportFlow (E := E) hMod t u))
        (modularTransportFlow (E := E) hMod t v) := by
            calc
              Q.berry (modularTransportFlow (E := E) hMod t u)
                  (modularTransportFlow (E := E) hMod t v)
                  =
                Q.metric (complex_i (E := E) (modularTransportFlow (E := E) hMod t u))
                  (modularTransportFlow (E := E) hMod t v) := by
                    exact Q.compat_complex_i _ _
              _ =
                Q.metric ((clockAxis (E := E)) (modularTransportFlow (E := E) hMod t u))
                  (modularTransportFlow (E := E) hMod t v) := by
                    simp
      _ =
      Q.metric (modularTransportFlow (E := E) hMod t ((clockAxis (E := E)) u))
        (modularTransportFlow (E := E) hMod t v) := by
            rw [hKu]
      _ = Q.metric ((clockAxis (E := E)) u) v := hMetric _ _
      _ = Q.berry u v := by
            calc
              Q.metric ((clockAxis (E := E)) u) v = Q.metric (complex_i (E := E) u) v := by
                simp
              _ = Q.berry u v := by
                symm
                exact Q.compat_complex_i u v

/--
If the modular transport generator lies on the local Cartan phase axis, then
the Hilbert-side operator metric is preserved along the corresponding exact
modular transport flow.
-/
theorem metricOfOperator_modularTransportFlow_eq_of_generator_eq_smul_phaseAxis
    (A hMod : EndH)
    (hComm :
      A.comp (clockAxis (E := E))
        =
      (clockAxis (E := E)).comp A)
    (σ t : ℝ)
    (hGen :
      modularTransportGenerator (E := E) hMod
        =
      σ • clockAxis (E := E)) :
    ∀ u v : H₂,
      metricOfOperator A
          (modularTransportFlow (E := E) hMod t u)
          (modularTransportFlow (E := E) hMod t v)
        =
      metricOfOperator A u v := by
  intro u v
  rw [modularTransportFlow_eq_KRotation_of_generator_eq_smul_phaseAxis
      (E := E) hMod σ t hGen]
  exact metricOfOperator_KRotation_eq_of_commute
    (E := E) (A := A) hComm (t * σ) u v

/--
If the modular transport generator lies on the local phase axis, then the
operatorial Berry seed is preserved along the exact modular transport flow.
-/
theorem berryOfOperator_modularTransportFlow_eq_of_generator_eq_smul_phaseAxis
    (A hMod : EndH)
    (hComm :
      A.comp (clockAxis (E := E))
        =
      (clockAxis (E := E)).comp A)
    (σ t : ℝ)
    (hGen :
      modularTransportGenerator (E := E) hMod
        =
      σ • clockAxis (E := E)) :
    ∀ u v : H₂,
      berryOfOperator (E := E) A
          (modularTransportFlow (E := E) hMod t u)
          (modularTransportFlow (E := E) hMod t v)
        =
      berryOfOperator (E := E) A u v := by
  intro u v
  rw [modularTransportFlow_eq_KRotation_of_generator_eq_smul_phaseAxis
      (E := E) hMod σ t hGen]
  exact berryOfOperator_KRotation_eq_of_commute
    (E := E) (A := A) hComm (t * σ) u v

/--
Split-`Cl(1,1)` (`J ∘ ε`) form of the phase-axis modular-flow invariance theorem
for the operatorial Berry seed.
-/
theorem berryTwoFormJEpsOfOperator_modularTransportFlow_eq_of_generator_eq_smul_phaseAxis
    (A hMod : EndH)
    (hComm :
      A.comp (clockAxis (E := E))
        =
      (clockAxis (E := E)).comp A)
    (σ t : ℝ)
    (hGen :
      modularTransportGenerator (E := E) hMod
        =
      σ • clockAxis (E := E)) :
    ∀ u v : H₂,
      berryTwoFormJEpsOfOperator (E := E) A
          (modularTransportFlow (E := E) hMod t u)
          (modularTransportFlow (E := E) hMod t v)
        =
      berryTwoFormJEpsOfOperator (E := E) A u v := by
  intro u v
  simpa [berryTwoFormJEpsOfOperator_eq_berryOfOperator (E := E) A] using
    berryOfOperator_modularTransportFlow_eq_of_generator_eq_smul_phaseAxis
      (E := E) (A := A) (hMod := hMod) hComm σ t hGen u v

/--
If the modular transport generator lies on the local Cartan phase axis, then
the Hilbert-side operatorial QGT is preserved along the corresponding exact
modular transport flow.
-/
theorem qgtOfOperator_modularTransportFlow_invariant_of_generator_eq_smul_phaseAxis
    (A hMod : EndH)
    (hA : IsSelfAdjoint A)
    (hComm :
      A.comp (clockAxis (E := E))
        =
      (clockAxis (E := E)).comp A)
    (σ t : ℝ)
    (hGen :
      modularTransportGenerator (E := E) hMod
        =
      σ • clockAxis (E := E)) :
    let Q := qgtOfOperator (E := E) A hA hComm
    (∀ u v : H₂,
      Q.metric (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.metric u v)
      ∧
    (∀ u v : H₂,
      Q.berry (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.berry u v) := by
  intro Q
  rw [modularTransportFlow_eq_KRotation_of_generator_eq_smul_phaseAxis
      (E := E) hMod σ t hGen]
  simpa using qgtOfOperator_KRotation_invariant
    (E := E) (A := A) hA hComm (t * σ)

/--
The operatorial Krein metric seed carried by a Cartan-odd / phase-antilinear
operator is invariant under the exact phase propagator `exp(tK)`.
-/
theorem kreinMetricOfOperator_KRotation_eq_of_IsPhaseAntilinear
    (A : EndH)
    (hAnti : IsPhaseAntilinear (E := E) A)
    (t : ℝ) :
    ∀ u v : H₂,
      kreinMetricOfOperator A
          (KRotation (E := E) t u)
          (KRotation (E := E) t v)
        =
      kreinMetricOfOperator A u v := by
  intro u v
  have hIntertwine :
      A.comp (KRotation (E := E) t) = (KRotation (E := E) (-t)).comp A :=
    comp_KRotation_eq_KRotation_neg_comp_of_IsPhaseAntilinear
      (E := E) (A := A) hAnti t
  have hEval : A (KRotation (E := E) t u) = KRotation (E := E) (-t) (A u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hIntertwine
  rw [kreinMetricOfOperator_apply, hEval, kreinMetricOfOperator_apply]
  exact kreinInner_KRotation_neg_left_KRotation_right (E := E) t (A u) v

/--
The operatorial Krein QGT built from a Krein-self-adjoint Cartan-odd seed is
preserved by the exact phase propagator `KRotation = exp(tK)`.
-/
theorem kreinQgtOfOperator_KRotation_invariant
    (A : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A)
    (t : ℝ) :
    let Q := kreinQgtOfOperator (E := E) A hA hAnti
    (∀ u v : H₂,
      Q.metric (KRotation (E := E) t u) (KRotation (E := E) t v) = Q.metric u v)
      ∧
    (∀ u v : H₂,
      Q.berry (KRotation (E := E) t u) (KRotation (E := E) t v) = Q.berry u v) := by
  intro Q
  refine ⟨?_, ?_⟩
  · intro u v
    exact kreinMetricOfOperator_KRotation_eq_of_IsPhaseAntilinear
      (E := E) (A := A) hAnti t u v
  · intro u v
    have hMetric :
        ∀ x y : H₂,
          Q.metric (KRotation (E := E) t x) (KRotation (E := E) t y) = Q.metric x y :=
      kreinMetricOfOperator_KRotation_eq_of_IsPhaseAntilinear
        (E := E) (A := A) hAnti t
    have hKComm :
        (clockAxis (E := E)).comp (KRotation (E := E) t)
          =
        (KRotation (E := E) t).comp (clockAxis (E := E)) := by
      exact comp_KRotation_eq_KRotation_comp_of_IsPhaseLinear
        (E := E)
        (A := clockAxis (E := E))
        (by simp [IsPhaseLinear])
        t
    have hKu :
        clockAxis (E := E) (KRotation (E := E) t u)
          =
        KRotation (E := E) t (clockAxis (E := E) u) := by
      simpa [ContinuousLinearMap.comp_apply] using congrArg (fun T : EndH => T u) hKComm
    calc
      Q.berry (KRotation (E := E) t u) (KRotation (E := E) t v)
        =
      Q.metric ((clockAxis (E := E)) (KRotation (E := E) t u)) (KRotation (E := E) t v) := by
            exact Q.compat _ _
      _ =
      Q.metric ((KRotation (E := E) t) ((clockAxis (E := E)) u)) (KRotation (E := E) t v) := by
            rw [hKu]
      _ = Q.metric ((clockAxis (E := E)) u) v := hMetric _ _
      _ = Q.berry u v := (Q.compat u v).symm

/--
If the modular transport generator lies on the local Cartan phase axis, then
the Krein-side operator metric is preserved along the corresponding exact
modular transport flow.
-/
theorem kreinMetricOfOperator_modularTransportFlow_eq_of_generator_eq_smul_phaseAxis
    (A hMod : EndH)
    (hAnti : IsPhaseAntilinear (E := E) A)
    (σ t : ℝ)
    (hGen :
      modularTransportGenerator (E := E) hMod
        =
      σ • clockAxis (E := E)) :
    ∀ u v : H₂,
      kreinMetricOfOperator A
          (modularTransportFlow (E := E) hMod t u)
          (modularTransportFlow (E := E) hMod t v)
        =
      kreinMetricOfOperator A u v := by
  intro u v
  rw [modularTransportFlow_eq_KRotation_of_generator_eq_smul_phaseAxis
      (E := E) hMod σ t hGen]
  exact kreinMetricOfOperator_KRotation_eq_of_IsPhaseAntilinear
    (E := E) (A := A) hAnti (t * σ) u v

/--
If the modular transport generator lies on the local Cartan phase axis, then
the Krein-side operatorial QGT is preserved along the corresponding exact
modular transport flow.
-/
theorem kreinQgtOfOperator_modularTransportFlow_invariant_of_generator_eq_smul_phaseAxis
    (A hMod : EndH)
    (hA : KreinSpace.IsKreinSelfAdjoint (H := H₂) A)
    (hAnti : IsPhaseAntilinear (E := E) A)
    (σ t : ℝ)
    (hGen :
      modularTransportGenerator (E := E) hMod
        =
      σ • clockAxis (E := E)) :
    let Q := kreinQgtOfOperator (E := E) A hA hAnti
    (∀ u v : H₂,
      Q.metric (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.metric u v)
      ∧
    (∀ u v : H₂,
      Q.berry (modularTransportFlow (E := E) hMod t u)
        (modularTransportFlow (E := E) hMod t v) = Q.berry u v) := by
  intro Q
  rw [modularTransportFlow_eq_KRotation_of_generator_eq_smul_phaseAxis
      (E := E) hMod σ t hGen]
  simpa using kreinQgtOfOperator_KRotation_invariant
    (E := E) (A := A) hA hAnti (t * σ)

end GeometricQuantumTensor

end InfoGeometry.Quantum
