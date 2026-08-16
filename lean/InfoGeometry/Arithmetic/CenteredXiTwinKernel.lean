import Mathlib.Analysis.Complex.Trigonometric
import InfoGeometry.Arithmetic.RiemannZetaEquivalences

/-!
# Centered completed-zeta twin kernel

This owner contains only the algebraic twin representation.  It reuses
`RiemannZetaEquivalences.symmetryAdaptedXi` and its proved evenness; it does
not assert a theta-kernel integral representation.  The latter remains an
explicit analytic target.

The nonzero-scale hypothesis in the affinity converse is intentional:
`(2 * z.re) * 0 = 0` contains no information about `z.re`.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.CenteredXiTwinKernel

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences

/-- The expanding member of the centered twin pair. -/
def twinPlus (z : ℂ) (u : ℝ) : ℂ := Complex.exp (z * (u : ℂ))

/-- The reflected member of the centered twin pair. -/
def twinMinus (z : ℂ) (u : ℝ) : ℂ := Complex.exp (-z * (u : ℂ))

/-- The algebraic hyperbolic imbalance of the twin pair. -/
def twinAffinity (z : ℂ) (u : ℝ) : ℝ := 2 * z.re * u

theorem twinPlus_neg (z : ℂ) (u : ℝ) :
    twinPlus (-z) u = twinMinus z u := by
  simp [twinPlus, twinMinus]

theorem twinMinus_neg (z : ℂ) (u : ℝ) :
    twinMinus (-z) u = twinPlus z u := by
  simp [twinPlus, twinMinus]

theorem twin_cosh (z : ℂ) (u : ℝ) :
    (twinPlus z u + twinMinus z u) / 2 = Complex.cosh (z * (u : ℂ)) := by
  simp [twinPlus, twinMinus, Complex.cosh]

theorem twinPlus_norm (z : ℂ) (u : ℝ) :
    ‖twinPlus z u‖ = Real.exp (z.re * u) := by
  simp [twinPlus, Complex.norm_exp, mul_re]

theorem twinMinus_norm (z : ℂ) (u : ℝ) :
    ‖twinMinus z u‖ = Real.exp (-z.re * u) := by
  simp [twinMinus, Complex.norm_exp, mul_re]

theorem twinAffinity_eq_log_norm_ratio (z : ℂ) (u : ℝ) :
    twinAffinity z u =
      Real.log (‖twinPlus z u‖ / ‖twinMinus z u‖) := by
  rw [twinPlus_norm, twinMinus_norm, ← Real.exp_sub]
  rw [Real.log_exp]
  simp [twinAffinity]
  ring

theorem twinAffinity_eq_zero_iff (z : ℂ) {u : ℝ} (hu : u ≠ 0) :
    twinAffinity z u = 0 ↔ z.re = 0 := by
  unfold twinAffinity
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact (hu h).elim
  · intro h
    simp [h]

theorem critical_twinAffinity (s : ℂ) (u : ℝ) :
    twinAffinity (s - (1 / 2 : ℂ)) u = (2 * s.re - 1) * u := by
  unfold twinAffinity
  have hhalf : ((1 / 2 : ℂ).re) = (1 / 2 : ℝ) := by norm_num
  rw [sub_re, hhalf]
  ring

theorem zero_affinity_iff_critical_line (s : ℂ) {u : ℝ} (hu : u ≠ 0) :
    twinAffinity (s - (1 / 2 : ℂ)) u = 0 ↔ s.re = 1 / 2 := by
  rw [critical_twinAffinity]
  constructor
  · intro h
    have hfac : 2 * s.re - 1 = 0 :=
      (mul_eq_zero.mp h).resolve_right hu
    linarith
  · intro h
    rw [h]
    ring

theorem balanced_twin_eq_cos (E u : ℝ) :
    (twinPlus ((E : ℂ) * Complex.I) u +
      twinMinus ((E : ℂ) * Complex.I) u) / 2 =
      (Real.cos (E * u) : ℂ) := by
  rw [twin_cosh]
  have harg : (E : ℂ) * Complex.I * (u : ℂ) =
      ((E * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.cosh_mul_I, Complex.ofReal_cos]

theorem centeredXi_twin_reflection (z : ℂ) :
    symmetryAdaptedXi z = symmetryAdaptedXi (-z) :=
  symmetryAdaptedXi_is_even z

/-! ## Abstract analytic target -/

/--
The theorem-honest interface for a future centered `Xi`/theta integral
representation.  This definition records the target without asserting that a
particular kernel or integration functional realizes it.
-/
def centeredXiThetaTwinIntegralTarget
    (Xi : ℂ → ℂ)
    (Phi : ℝ → ℂ)
    (integral : (ℝ → ℂ) → ℂ) : Prop :=
  ∀ z : ℂ,
    Xi z = integral (fun u => Phi u * ((twinPlus z u + twinMinus z u) / 2))

theorem centeredXiThetaTwinIntegralTarget_iff_cosh
    (Xi : ℂ → ℂ)
    (Phi : ℝ → ℂ)
    (integral : (ℝ → ℂ) → ℂ) :
    centeredXiThetaTwinIntegralTarget Xi Phi integral ↔
      ∀ z : ℂ,
        Xi z = integral (fun u => Phi u * Complex.cosh (z * (u : ℂ))) := by
  constructor
  · intro h z
    simpa only [centeredXiThetaTwinIntegralTarget, twin_cosh] using h z
  · intro h z
    simpa only [centeredXiThetaTwinIntegralTarget, twin_cosh] using h z

end InfoGeometry.Arithmetic.CenteredXiTwinKernel
