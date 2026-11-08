/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Physics.NuclearRealKreinObservables

/-!
# Two real quadratures of a transported transition

The native real `clockAxis` supplies the second quadrature. Their sum of
squares is invariant under independent real clock rotations of the two
external states, provided the supplied transition intertwines the clocks.
Both quadratures use the same wave embeddings and positive induced norms.
This is a bounded real transition strength, with no assertion that a supplied
operator is a physical multipole or that its strength is at most one.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearRealClockTransitionStrength

open ContinuousLinearMap InfoGeometry.Krein
open InfoGeometry.Krein.BornRuleCore
open InfoGeometry.Physics.NuclearEffectiveObservables

section Quadratures

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Sum of squares of the two native real readouts. -/
def twoQuadratureStrength (f v : DoubledSpace E) : ℝ :=
  kreinAdaptedAmplitude f v ^ 2 +
    kreinAdaptedAmplitude f (clockAxis v) ^ 2

theorem twoQuadratureStrength_nonneg (f v : DoubledSpace E) :
    0 ≤ twoQuadratureStrength f v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem clock_inner_skew (f v : DoubledSpace E) :
    inner ℝ (clockAxis f) v = -inner ℝ f (clockAxis v) := by
  simp [clockAxis_apply, WithLp.prod_inner_apply] <;> ring

private theorem clock_inner_comp (f v : DoubledSpace E) :
    inner ℝ (clockAxis f) (clockAxis v) = inner ℝ f v := by
  simp [clockAxis_apply, WithLp.prod_inner_apply, add_comm]

private theorem clock_clock (v : DoubledSpace E) :
    clockAxis (clockAxis v) = -v := by
  have h := congrArg (fun A : DoubledSpace E →L[ℝ] DoubledSpace E => A v)
    (clockAxis_sq E)
  simpa only [comp_apply, neg_apply, id_apply] using h

theorem twoQuadratureStrength_rotate_left (f v : DoubledSpace E)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    twoQuadratureStrength (c • f + s • clockAxis f) v =
      twoQuadratureStrength f v := by
  simp only [twoQuadratureStrength, kreinAdaptedAmplitude_eq_inner,
    inner_add_left, real_inner_smul_left]
  rw [clock_inner_skew, clock_inner_comp]
  calc
    (c * inner ℝ f v + s * -inner ℝ f (clockAxis v)) ^ 2 +
        (c * inner ℝ f (clockAxis v) + s * inner ℝ f v) ^ 2 =
      (c ^ 2 + s ^ 2) *
        ((inner ℝ f v) ^ 2 + (inner ℝ f (clockAxis v)) ^ 2) := by ring
    _ = _ := by rw [hcs, one_mul]

theorem twoQuadratureStrength_rotate_right (f v : DoubledSpace E)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    twoQuadratureStrength f (c • v + s • clockAxis v) =
      twoQuadratureStrength f v := by
  simp only [twoQuadratureStrength, kreinAdaptedAmplitude_eq_inner,
    map_add, map_smul, inner_add_right, real_inner_smul_right,
    clock_clock, inner_neg_right]
  calc
    (c * inner ℝ f v + s * inner ℝ f (clockAxis v)) ^ 2 +
        (c * inner ℝ f (clockAxis v) + s * -inner ℝ f v) ^ 2 =
      (c ^ 2 + s ^ 2) *
        ((inner ℝ f v) ^ 2 + (inner ℝ f (clockAxis v)) ^ 2) := by ring
    _ = _ := by rw [hcs, one_mul]

theorem norm_sq_clock_rotation (v : DoubledSpace E)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ‖c • v + s • clockAxis v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h : inner ℝ (c • v + s • clockAxis v) (c • v + s • clockAxis v) =
      (c ^ 2 + s ^ 2) * inner ℝ v v := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [clock_inner_skew v v, clock_inner_comp v v]
    ring
  simpa only [hcs, one_mul, real_inner_self_eq_norm_sq] using h

end Quadratures

section RectangularTransitions

variable {Ei Ef : Type*}
variable [NormedAddCommGroup Ei] [InnerProductSpace ℝ Ei] [CompleteSpace Ei]
variable [NormedAddCommGroup Ef] [InnerProductSpace ℝ Ef] [CompleteSpace Ef]

/-- The external-state norms, rather than the norm of the transition image,
normalize an arbitrary supplied transition. -/
def transitionStrength (O : DoubledSpace Ei →L[ℝ] DoubledSpace Ef)
    (xi : DoubledSpace Ei) (xf : DoubledSpace Ef) : ℝ :=
  twoQuadratureStrength xf (O xi) / (‖xf‖ ^ 2 * ‖xi‖ ^ 2)

theorem transitionStrength_nonneg (O : DoubledSpace Ei →L[ℝ] DoubledSpace Ef)
    (xi : DoubledSpace Ei) (xf : DoubledSpace Ef) :
    0 ≤ transitionStrength O xi xf :=
  div_nonneg (twoQuadratureStrength_nonneg _ _)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The two endpoint rotations are independent. Input rotation invariance
requires the transition to intertwine the native real clocks. -/
theorem transitionStrength_independent_clock_rotations
    (O : DoubledSpace Ei →L[ℝ] DoubledSpace Ef)
    (hO : O.comp (clockAxis (E := Ei)) = (clockAxis (E := Ef)).comp O)
    (xi : DoubledSpace Ei) (xf : DoubledSpace Ef)
    (ci si cf sf : ℝ) (hi : ci ^ 2 + si ^ 2 = 1) (hf : cf ^ 2 + sf ^ 2 = 1) :
    transitionStrength O (ci • xi + si • clockAxis xi)
        (cf • xf + sf • clockAxis xf) = transitionStrength O xi xf := by
  have hOi : O (clockAxis xi) = clockAxis (O xi) := by
    exact congrArg (fun A : DoubledSpace Ei →L[ℝ] DoubledSpace Ef => A xi) hO
  unfold transitionStrength
  rw [map_add, map_smul, map_smul, hOi,
    twoQuadratureStrength_rotate_left _ _ cf sf hf,
    twoQuadratureStrength_rotate_right _ _ ci si hi,
    norm_sq_clock_rotation _ cf sf hf, norm_sq_clock_rotation _ ci si hi]

end RectangularTransitions

section EffectiveTransport

variable {Mi Mf Hi Ef : Type*}
variable [NormedAddCommGroup Mi] [InnerProductSpace ℝ Mi] [CompleteSpace Mi]
variable [NormedAddCommGroup Mf] [InnerProductSpace ℝ Mf] [CompleteSpace Mf]
variable [NormedAddCommGroup Hi] [InnerProductSpace ℝ Hi] [CompleteSpace Hi]
variable [NormedAddCommGroup Ef] [InnerProductSpace ℝ Ef] [CompleteSpace Ef]

/-- Each quadrature is transported through the existing effective operator.
The two external Gram factors are shared by the two quadratures. -/
theorem normalized_twoQuadratureStrength
    (Ωi : Mi →L[ℝ] Hi) (Ωf : Mf →L[ℝ] DoubledSpace Ef)
    (O : Hi →L[ℝ] DoubledSpace Ef) (xi : Mi) (xf : Mf) :
    twoQuadratureStrength (normalizedState Ωf xf) (O (normalizedState Ωi xi)) =
      ((inner ℝ xf (effectiveOperator Ωi Ωf O xi)) ^ 2 +
        (inner ℝ xf (effectiveOperator Ωi Ωf ((clockAxis (E := Ef)).comp O) xi)) ^ 2) /
        (metricWeight Ωf xf * metricWeight Ωi xi) := by
  have h0 := normalized_transition_strength (𝕜 := ℝ) Ωi Ωf O xi xf
  have h1 := normalized_transition_strength (𝕜 := ℝ)
    Ωi Ωf ((clockAxis (E := Ef)).comp O) xi xf
  simp only [Real.norm_eq_abs, sq_abs] at h0 h1
  simp only [twoQuadratureStrength, kreinAdaptedAmplitude_eq_inner]
  change (inner ℝ (normalizedState Ωf xf) (O (normalizedState Ωi xi))) ^ 2 +
      (inner ℝ (normalizedState Ωf xf)
        (((clockAxis (E := Ef)).comp O) (normalizedState Ωi xi))) ^ 2 = _
  rw [h0, h1, ← add_div]

end EffectiveTransport

end InfoGeometry.Physics.NuclearRealClockTransitionStrength
