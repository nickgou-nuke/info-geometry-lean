import InfoGeometry.Quantum.GeometricTensorOperatorLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.GeometricTensorPolarizedPullback
import InfoGeometry.Canonical.BogoliubovFrameKreinMetricBridge

/-!
# QGT metric readout of Bogoliubov frame transport

The operator-valued pullback metric and the operatorial QGT metric seed are
the same construction at different readout levels.  This file records the
actual equality between those two levels and its vielbein specialization.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Quantum.GeometricQuantumTensor

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.BogoliubovVielbein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

theorem metricOfOperator_pullbackMetric_apply
  (U G : EndH) (u v : H₂) :
    metricOfOperator (E := E)
        (InfoGeometry.Canonical.pullbackMetric U G) u v =
      ⟪G (U u), U v⟫_ℝ := by
  rw [metricOfOperator_apply]
  change ⟪(ContinuousLinearMap.adjoint U) (G (U u)), v⟫_ℝ = _
  rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_right]
  exact real_inner_comm _ _

theorem hasDerivAt_metricOfOperator_pullbackMetric_apply
    (U U' : ℝ → EndH) (G : EndH) (t : ℝ) (u v : H₂)
    (hU : HasDerivAt U (U' t) t) :
    HasDerivAt
      (fun s => metricOfOperator (E := E)
        (InfoGeometry.Canonical.pullbackMetric (U s) G) u v)
      (⟪G (U t u), U' t v⟫_ℝ +
        ⟪G (U' t u), U t v⟫_ℝ) t := by
  have hu : HasDerivAt (fun s => U s u) (U' t u) t := by
    simpa using hU.clm_apply (hasDerivAt_const (x := t) (c := u))
  have hv : HasDerivAt (fun s => U s v) (U' t v) t := by
    simpa using hU.clm_apply (hasDerivAt_const (x := t) (c := v))
  have hGu : HasDerivAt (fun s => G (U s u)) (G (U' t u)) t := by
    simpa using
      (hasDerivAt_const (x := t) (c := G)).clm_apply hu
  have hInner := hGu.inner ℝ hv
  have hfun :
      (fun s => metricOfOperator (E := E)
        (InfoGeometry.Canonical.pullbackMetric (U s) G) u v) =
        (fun s => ⟪G (U s u), U s v⟫_ℝ) := by
    funext s
    exact metricOfOperator_pullbackMetric_apply (U s) G u v
  rw [hfun]
  simpa [add_assoc] using hInner

theorem hasDerivAt_metricOfOperator_polarizedPullbackMetric_apply
    (Uplus Uplus' Uminus Uminus' : ℝ → EndH) (G : EndH) (t : ℝ)
    (u v : H₂)
    (hplus : HasDerivAt Uplus (Uplus' t) t)
    (hminus : HasDerivAt Uminus (Uminus' t) t) :
    HasDerivAt
      (fun s => metricOfOperator (E := E)
        (polarizedPullbackMetric (Uplus s) (Uminus s) G) u v)
      (⟪G (Uplus t u), Uminus' t v⟫_ℝ +
        ⟪G (Uplus' t u), Uminus t v⟫_ℝ) t := by
  have hu : HasDerivAt (fun s => Uplus s u) (Uplus' t u) t := by
    simpa using hplus.clm_apply (hasDerivAt_const (x := t) (c := u))
  have hv : HasDerivAt (fun s => Uminus s v) (Uminus' t v) t := by
    simpa using hminus.clm_apply (hasDerivAt_const (x := t) (c := v))
  have hGu : HasDerivAt (fun s => G (Uplus s u)) (G (Uplus' t u)) t := by
    simpa using (hasDerivAt_const (x := t) (c := G)).clm_apply hu
  have hInner := hGu.inner ℝ hv
  have hfun :
      (fun s => metricOfOperator (E := E)
        (polarizedPullbackMetric (Uplus s) (Uminus s) G) u v) =
        (fun s => ⟪G (Uplus s u), Uminus s v⟫_ℝ) := by
    funext s
    simpa [metricOfOperator] using
      (metricOfOperator_polarizedPullbackMetric_apply
        (Uplus s) (Uminus s) G u v)
  rw [hfun]
  simpa [add_assoc] using hInner

theorem deriv_metricOfOperator_polarizedPullbackMetric_apply
    (Uplus Uplus' Uminus Uminus' : ℝ → EndH) (G : EndH) (t : ℝ)
    (u v : H₂)
    (hplus : HasDerivAt Uplus (Uplus' t) t)
    (hminus : HasDerivAt Uminus (Uminus' t) t) :
    deriv
      (fun s => metricOfOperator (E := E)
        (polarizedPullbackMetric (Uplus s) (Uminus s) G) u v) t =
      (⟪G (Uplus t u), Uminus' t v⟫_ℝ +
        ⟪G (Uplus' t u), Uminus t v⟫_ℝ) := by
  exact (hasDerivAt_metricOfOperator_polarizedPullbackMetric_apply
    Uplus Uplus' Uminus Uminus' G t u v hplus hminus).deriv

theorem hasDerivAt_metricOfOperator_transportedKreinMetric_apply
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ)
    (u v : H₂) :
    HasDerivAt
      (fun s => metricOfOperator (E := E)
        (transportedKreinMetric V G₀ s) u v)
      (⟪G₀ (V.localFrame t u),
          InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature t v⟫_ℝ +
        ⟪G₀ (InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature t u),
          V.localFrame t v⟫_ℝ) t := by
  apply hasDerivAt_metricOfOperator_pullbackMetric_apply
    (U := fun s => V.localFrame s)
    (U' := fun s => InfoGeometry.Canonical.expTransport (A := EndH)
      V.connectionGenerator V.maurerCartanCurvature s)
    (G := G₀) (t := t) (u := u) (v := v)
  simpa [BogoliubovVielbeinBundle.localFrame,
    BogoliubovVielbeinBundle.maurerCartanCurvature,
    InfoGeometry.Canonical.BerryPhase.hestenesMaurerCartanCurvature] using
    (InfoGeometry.Canonical.hasDerivAt_expTransport
      (A := EndH) V.connectionGenerator V.reference t)

theorem deriv_metricOfOperator_transportedKreinMetric_apply
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ)
    (u v : H₂) :
    deriv
      (fun s => metricOfOperator (E := E)
        (transportedKreinMetric V G₀ s) u v) t =
      (⟪G₀ (V.localFrame t u),
          InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature t v⟫_ℝ +
        ⟪G₀ (InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature t u),
          V.localFrame t v⟫_ℝ) := by
  exact (hasDerivAt_metricOfOperator_transportedKreinMetric_apply
    (V := V) (G₀ := G₀) (t := t) (u := u) (v := v)).deriv

theorem hasDerivAt_berryOfOperator_transportedKreinMetric_apply
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ)
    (u v : H₂) :
    HasDerivAt
      (fun s => berryOfOperator (E := E)
        (transportedKreinMetric V G₀ s) u v)
      (⟪G₀ (V.localFrame t
          (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u)),
          InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature t v⟫_ℝ +
        ⟪G₀ (InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature t
              (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u)),
          V.localFrame t v⟫_ℝ) t := by
  simpa [berryOfOperator_apply] using
    (hasDerivAt_metricOfOperator_transportedKreinMetric_apply
      (V := V) (G₀ := G₀) (t := t)
      (u := InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) (v := v))

theorem deriv_berryOfOperator_transportedKreinMetric_apply
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ)
    (u v : H₂) :
    deriv
      (fun s => berryOfOperator (E := E)
        (transportedKreinMetric V G₀ s) u v) t =
      (⟪G₀ (V.localFrame t
          (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u)),
          InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature t v⟫_ℝ +
        ⟪G₀ (InfoGeometry.Canonical.expTransport (A := EndH)
            V.connectionGenerator V.maurerCartanCurvature t
              (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u)),
          V.localFrame t v⟫_ℝ) := by
  exact (hasDerivAt_berryOfOperator_transportedKreinMetric_apply
    (V := V) (G₀ := G₀) (t := t) (u := u) (v := v)).deriv

theorem deriv_metricOfOperator_transportedKreinMetric_swap
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ)
    (hG : ContinuousLinearMap.adjoint G₀ = G₀) (u v : H₂) :
    deriv
      (fun s => metricOfOperator (E := E)
        (transportedKreinMetric V G₀ s) u v) t =
      deriv
        (fun s => metricOfOperator (E := E)
          (transportedKreinMetric V G₀ s) v u) t := by
  rw [deriv_metricOfOperator_transportedKreinMetric_apply,
    deriv_metricOfOperator_transportedKreinMetric_apply]
  have hpair : ∀ x y : H₂, ⟪G₀ x, y⟫_ℝ = ⟪G₀ y, x⟫_ℝ := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_right, hG]
    exact real_inner_comm _ _
  rw [hpair (V.localFrame t u)
      (InfoGeometry.Canonical.expTransport (A := EndH)
        V.connectionGenerator V.maurerCartanCurvature t v)]
  rw [hpair (V.localFrame t v)
      (InfoGeometry.Canonical.expTransport (A := EndH)
        V.connectionGenerator V.maurerCartanCurvature t u)]
  ac_rfl

theorem deriv_metricOfOperator_transportedKreinMetric_curvature
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ)
    (u v : H₂) :
    deriv
      (fun s => metricOfOperator (E := E)
        (transportedKreinMetric V G₀ s) u v) t =
      (⟪G₀ (V.localFrame t u),
          V.transportedMaurerCartanCurvature t v⟫_ℝ +
        ⟪G₀ (V.transportedMaurerCartanCurvature t u),
          V.localFrame t v⟫_ℝ) := by
  rw [deriv_metricOfOperator_transportedKreinMetric_apply]
  rw [V.transportedMaurerCartanCurvature_eq_expTransport_maurerCartanCurvature t]

theorem metricOfOperator_transportedKreinMetric_apply
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ)
    (u v : H₂) :
    metricOfOperator (E := E)
        (transportedKreinMetric V G₀ t) u v =
      ⟪G₀ (V.localFrame t u), V.localFrame t v⟫_ℝ := by
  exact metricOfOperator_pullbackMetric_apply (V.localFrame t) G₀ u v

theorem metricOfOperator_transportedKreinMetric_swap
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ)
    (hG : ContinuousLinearMap.adjoint G₀ = G₀) (u v : H₂) :
    metricOfOperator (E := E)
        (transportedKreinMetric V G₀ t) u v =
      metricOfOperator (E := E)
        (transportedKreinMetric V G₀ t) v u := by
  rw [metricOfOperator_transportedKreinMetric_apply,
    metricOfOperator_transportedKreinMetric_apply]
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [hG]
  exact real_inner_comm _ _

theorem berryOfOperator_transportedKreinMetric_apply
    (V : BogoliubovVielbeinBundle (E := E)) (G₀ : EndH) (t : ℝ)
    (u v : H₂) :
    berryOfOperator (E := E)
        (transportedKreinMetric V G₀ t) u v =
      ⟪G₀ (V.localFrame t
          (InfoGeometry.Canonical.TomitaTakesaki.clockAxis u)),
        V.localFrame t v⟫_ℝ := by
  rw [berryOfOperator_apply]
  exact metricOfOperator_transportedKreinMetric_apply
    (V := V) (G₀ := G₀) (t := t)
    (u := InfoGeometry.Canonical.TomitaTakesaki.clockAxis u) (v := v)

end InfoGeometry.Quantum.GeometricQuantumTensor
