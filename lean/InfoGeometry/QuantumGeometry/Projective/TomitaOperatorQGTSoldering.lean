import InfoGeometry.QuantumGeometry.Projective.QGT
import InfoGeometry.Quantum.GeometricTensorOperatorLift
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic


/-!
# Tomita/Hestenes operator tensor to projective QGT soldering

The native doubled carrier `DoubledSpace H = WithLp 2 (H × H)` is simultaneously
available as a complex Nambu Hilbert space when `H` is complex and, after
`InnerProductSpace.complexToReal`, as the real doubled Hilbert carrier used by
the Tomita/Hestenes operator tensor.

This file proves the actual identification on the positive Hestenes polarization
sector.  The doubled phase axis

`K(x, ξ) = (-ξ, x)`

is promoted to a complex-linear operator.  If the normalized state is in the
`+i` eigenspace and a tangent generator commutes with `K`, then its horizontal
projective tangent vector is again in the `+i` eigenspace.  Consequently the
real operator metric is exactly the Fubini--Study metric and the real
operatorial Berry seed is exactly `-1/2` of the projective Berry curvature.

No new geometric structure is assumed: the proof uses the existing doubled
phase axis, Mathlib's complex-to-real inner-product restriction, and the native
projective QGT Gram identity.
-/

noncomputable section

namespace InfoGeometry.QuantumGeometry.Projective.TomitaOperatorQGTSoldering

open scoped InnerProductSpace
open ContinuousLinearMap
open InfoGeometry.Krein
open InfoGeometry.Quantum.GeometricQuantumTensor
open InfoGeometry.QuantumGeometry.Projective

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "NambuH" => DoubledSpace H
local notation "EndC" => NambuH →L[ℂ] NambuH

/-- Use Mathlib's canonical real restriction of the complex Hilbert structure. -/
local instance complexBaseRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

/--
The doubled Hestenes/Tomita phase axis regarded as a complex-linear operator on
the Nambu Hilbert carrier.
-/
noncomputable def nambuClockAxis : EndC where
  toFun := fun u => clockAxis (E := H) u
  map_add' := by
    intro u v
    exact (clockAxis (E := H)).map_add u v
  map_smul' := by
    intro c u
    change complex_i (c • u) = c • complex_i u
    apply DoubledSpace.ext
    simp only [complex_i_apply, WithLp.toLp_smul, smul_fst, smul_snd]
  cont := (clockAxis (E := H)).cont

@[simp]
theorem nambuClockAxis_apply (u : NambuH) :
    nambuClockAxis (H := H) u = clockAxis (E := H) u := by
  rfl

/-- The complex and real readouts of the phase axis are literally the same map. -/
theorem nambuClockAxis_restrictScalars_eq_clockAxis :
    (nambuClockAxis (H := H)).restrictScalars ℝ = clockAxis (E := H) := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

/-- The Nambu phase axis squares to `-1` also as a complex-linear operator. -/
@[simp]
theorem nambuClockAxis_sq :
    (nambuClockAxis (H := H)).comp (nambuClockAxis (H := H)) =
      -(ContinuousLinearMap.id ℂ NambuH) := by
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg
    (fun T : NambuH →L[ℝ] NambuH => T u)
    (clockAxis_sq (E := H))
  simpa [nambuClockAxis, ContinuousLinearMap.comp_apply] using h

/-- Positive Hestenes polarization: `K ψ = i ψ`. -/
def IsPositiveClockPolarized (u : NambuH) : Prop :=
  nambuClockAxis (H := H) u = Complex.I • u

/-- A complex tangent generator is phase-linear when it commutes with `K`. -/
def CommutesClock (X : EndC) : Prop :=
  X.comp (nambuClockAxis (H := H)) = (nambuClockAxis (H := H)).comp X

/-- A phase-linear generator preserves the positive Hestenes polarization. -/
theorem apply_positiveClockPolarized
    (X : EndC) (u : NambuH)
    (hX : CommutesClock X)
    (hu : IsPositiveClockPolarized u) :
    IsPositiveClockPolarized (X u) := by
  unfold CommutesClock at hX
  unfold IsPositiveClockPolarized at hu ⊢
  have hx := congrArg (fun T : EndC => T u) hX
  change X (nambuClockAxis (H := H) u) = nambuClockAxis (H := H) (X u) at hx
  rw [hu] at hx
  rw [map_smul] at hx
  exact hx.symm

/--
Horizontal projection preserves the positive Hestenes polarization for a
phase-linear tangent generator.
-/
theorem projOrth_positiveClockPolarized
    (ψ : NormalizedState NambuH)
    (X : EndC)
    (hψ : IsPositiveClockPolarized ψ.vec)
    (hX : CommutesClock X) :
    IsPositiveClockPolarized (projOrth ψ X) := by
  unfold IsPositiveClockPolarized projOrth
  rw [map_sub, map_smul, hψ]
  have hXu := apply_positiveClockPolarized X ψ.vec hX hψ
  unfold IsPositiveClockPolarized at hXu
  rw [hXu]
  module

/--
The real inner product obtained from the complex Hilbert structure commutes
with the doubled `L²` product: it is the real part of the complex Nambu inner
product.
-/
theorem nambu_real_inner_eq_re_complex_inner (u v : NambuH) :
    ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := by
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  rw [real_inner_eq_re_inner ℂ (u.ofLp.2) (v.ofLp.2)]
  rw [← Complex.add_re]

/-- Operatorial real metric evaluated on projective horizontal tangent vectors. -/
noncomputable def horizontalOperatorMetric
    (ψ : NormalizedState NambuH)
    (X Y : EndC) : ℝ :=
  metricOfOperator (E := H)
    (ContinuousLinearMap.id ℝ NambuH)
    (projOrth ψ X) (projOrth ψ Y)

/-- Operatorial Hestenes Berry seed evaluated on projective horizontal tangents. -/
noncomputable def horizontalOperatorBerry
    (ψ : NormalizedState NambuH)
    (X Y : EndC) : ℝ :=
  berryOfOperator (E := H)
    (ContinuousLinearMap.id ℝ NambuH)
    (projOrth ψ X) (projOrth ψ Y)

/--
Exact metric soldering: the real operator metric on horizontal vectors is the
Fubini--Study metric.
-/
theorem horizontalOperatorMetric_eq_fubiniStudyMetric
    (ψ : NormalizedState NambuH)
    (X Y : EndC) :
    horizontalOperatorMetric ψ X Y =
      fubiniStudyMetric ψ X Y := by
  unfold horizontalOperatorMetric
  rw [metricOfOperator_apply]
  simp only [ContinuousLinearMap.id_apply]
  rw [nambu_real_inner_eq_re_complex_inner]
  unfold fubiniStudyMetric
  rw [← QGT_eq_inner_projOrth]

/-- On the positive polarization sector the operatorial Berry seed is `Im Q`. -/
theorem horizontalOperatorBerry_eq_QGT_im
    (ψ : NormalizedState NambuH)
    (X Y : EndC)
    (hψ : IsPositiveClockPolarized ψ.vec)
    (hX : CommutesClock X) :
    horizontalOperatorBerry ψ X Y =
      (QGT ψ X Y).im := by
  let u := projOrth ψ X
  let v := projOrth ψ Y
  have hu : IsPositiveClockPolarized u := by
    simpa [u] using projOrth_positiveClockPolarized ψ X hψ hX
  have hQ : QGT ψ X Y = ⟪u, v⟫_ℂ := by
    simpa [u, v] using QGT_eq_inner_projOrth ψ X Y
  unfold horizontalOperatorBerry
  rw [berryOfOperator_apply, metricOfOperator_apply]
  simp only [ContinuousLinearMap.id_apply]
  change ⟪clockAxis (E := H) u, v⟫_ℝ = (QGT ψ X Y).im
  rw [nambu_real_inner_eq_re_complex_inner]
  change (⟪nambuClockAxis (H := H) u, v⟫_ℂ).re = (QGT ψ X Y).im
  unfold IsPositiveClockPolarized at hu
  rw [hu, inner_smul_left]
  rw [hQ]
  simp [Complex.mul_re]

/--
Exact symplectic soldering on the positive Hestenes polarization sector:
projective Berry curvature is `-2` times the operatorial Hestenes Berry seed.
-/
theorem berryCurvature_eq_neg_two_horizontalOperatorBerry
    (ψ : NormalizedState NambuH)
    (X Y : EndC)
    (hψ : IsPositiveClockPolarized ψ.vec)
    (hX : CommutesClock X) :
    berryCurvature ψ X Y =
      -2 * horizontalOperatorBerry ψ X Y := by
  rw [horizontalOperatorBerry_eq_QGT_im ψ X Y hψ hX]
  rfl

/--
Complete theorem-level Tomita/Hestenes-to-projective-QGT soldering packet.
Both tangent generators are required to preserve the polarization so the same
statement is stable under exchanging the two tangent directions.
-/
theorem tomitaOperator_projectiveQGT_soldering
    (ψ : NormalizedState NambuH)
    (X Y : EndC)
    (hψ : IsPositiveClockPolarized ψ.vec)
    (hX : CommutesClock X)
    (hY : CommutesClock Y) :
    horizontalOperatorMetric ψ X Y = fubiniStudyMetric ψ X Y ∧
    berryCurvature ψ X Y = -2 * horizontalOperatorBerry ψ X Y ∧
    IsPositiveClockPolarized (projOrth ψ X) ∧
    IsPositiveClockPolarized (projOrth ψ Y) := by
  exact ⟨
    horizontalOperatorMetric_eq_fubiniStudyMetric ψ X Y,
    berryCurvature_eq_neg_two_horizontalOperatorBerry ψ X Y hψ hX,
    projOrth_positiveClockPolarized ψ X hψ hX,
    projOrth_positiveClockPolarized ψ Y hψ hY⟩

end InfoGeometry.QuantumGeometry.Projective.TomitaOperatorQGTSoldering

end noncomputable section
