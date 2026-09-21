import InfoGeometry.Canonical.SpinorHydrodynamicReadout
import InfoGeometry.External.Auto.SarsModularWeakValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# An exact two-state spatial momentum readout

The preparation `(1, exp (I*y))` has an actual spatial derivative. Applying
`-I` to that derivative gives `(0, exp (I*y))`. Against the postselection
`(d-r, r*exp (I*y))`, its weak numerator is `r` and its overlap is `d`.
Consequently the regular real velocity component is `r/d`.

Both boundary states are smooth, including at `d = 0`. The matrix below is
the action of this momentum on the specified preparation family; it is not
asserted to represent the differential operator on arbitrary spatial fields.
No wave evolution equation or conservation of the indefinite norm is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwoStateMomentumShear

open scoped InnerProductSpace ContDiff
open SarsModularWeakValue

abbrev Spinor := EuclideanSpace ℂ (Fin 2)

def phase (y : ℝ) : ℂ := Complex.exp ((y : ℂ) * Complex.I)

def rawPre (y : ℝ) : State2 := ![1, phase y]

def rawPost (d r y : ℝ) : State2 := ![(d - r : ℝ), (r : ℂ) * phase y]

def pre (y : ℝ) : Spinor := WithLp.toLp 2 (rawPre y)

def post (d r y : ℝ) : Spinor := WithLp.toLp 2 (rawPost d r y)

def dyPre (y : ℝ) : Spinor := !₂[0, phase y * Complex.I]

def momentum (y : ℝ) : Spinor := (-Complex.I) • dyPre y

def weakReadout (d r y : ℝ) : ℝ :=
  (inner ℂ (post d r y) (momentum y) / inner ℂ (post d r y) (pre y)).re

theorem pre_ne_zero (y : ℝ) : pre y ≠ 0 := by
  intro h
  have hc := congrArg (fun v : Spinor => v 0) h
  simp [pre, rawPre] at hc

theorem post_at_node_ne_zero {r : ℝ} (hr : r ≠ 0) (y : ℝ) : post 0 r y ≠ 0 := by
  intro h
  have hc := congrArg (fun v : Spinor => v 0) h
  simp [post, rawPost, hr] at hc

theorem norm_phase (y : ℝ) : ‖phase y‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I y

theorem conj_phase_mul (y : ℝ) : star (phase y) * phase y = 1 := by
  have h := Complex.conj_mul' (phase y)
  simpa [norm_phase] using h

theorem hasDerivAt_phase (y : ℝ) :
    HasDerivAt phase (phase y * Complex.I) y := by
  simpa [phase] using
    (((hasDerivAt_id y).ofReal_comp.mul_const Complex.I).cexp)

theorem hasDerivAt_pre (y : ℝ) : HasDerivAt pre (dyPre y) y := by
  have hp : HasDerivAt rawPre (![0, phase y * Complex.I]) y := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [rawPre] using hasDerivAt_const y (1 : ℂ)
    · simpa [rawPre] using hasDerivAt_phase y
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt y hp

theorem momentum_eq (y : ℝ) : momentum y = !₂[0, phase y] := by
  have hi : (-Complex.I) * (phase y * Complex.I) = phase y := by
    calc
      _ = phase y * (-(Complex.I * Complex.I)) := by ring
      _ = phase y := by simp
  ext i
  fin_cases i
  · simp [momentum, dyPre]
  · simpa [momentum, dyPre, neg_mul] using hi

theorem momentum_eq_actual_derivative (y : ℝ) :
    momentum y = (-Complex.I) • deriv pre y := by
  rw [(hasDerivAt_pre y).deriv]
  rfl

theorem cinner_eq_inner (u v : State2) :
    cinner u v = inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
  simp [cinner, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

theorem overlap_eq (d r y : ℝ) : inner ℂ (post d r y) (pre y) = (d : ℂ) := by
  change inner ℂ (WithLp.toLp 2 (rawPost d r y))
    (WithLp.toLp 2 (rawPre y)) = (d : ℂ)
  rw [← cinner_eq_inner]
  simp only [cinner, rawPost, rawPre, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, star_mul, Complex.star_def, Complex.conj_ofReal, mul_one]
  calc
    _ = (d - r : ℝ) + (r : ℂ) * (star (phase y) * phase y) := by
      simp only [Complex.star_def]; ring
    _ = (d : ℂ) := by rw [conj_phase_mul]; push_cast; ring

theorem numerator_eq (d r y : ℝ) :
    inner ℂ (post d r y) (momentum y) = (r : ℂ) := by
  rw [momentum_eq]
  change inner ℂ (WithLp.toLp 2 (rawPost d r y))
    (WithLp.toLp 2 (![0, phase y] : State2)) = (r : ℂ)
  rw [← cinner_eq_inner]
  simp only [cinner, rawPost, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_zero, zero_add, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  calc
    _ = (r : ℂ) * (star (phase y) * phase y) := by
      simp only [Complex.star_def]; ring
    _ = (r : ℂ) := by rw [conj_phase_mul, mul_one]

theorem weakReadout_eq (d r y : ℝ) : weakReadout d r y = r / d := by
  rw [weakReadout, numerator_eq, overlap_eq]
  simp [← Complex.ofReal_div]

/-- The preparation has zero momentum in either spatial coordinate on which
it does not depend. This uses the derivative of the constant curve. -/
theorem transverse_momentum_readout_zero (d r y x : ℝ) :
    (inner ℂ (post d r y)
      ((-Complex.I) • deriv (fun _ : ℝ => pre y) x) /
        inner ℂ (post d r y) (pre y)).re = 0 := by
  simp

/-- This matrix agrees with `-I*∂_y` on the preparation family above. -/
def momentumMatrix : M2C := !![0, 0; 0, 1]

theorem matVec_momentumMatrix (y : ℝ) :
    matVec momentumMatrix (rawPre y) = ![0, phase y] := by
  funext i
  fin_cases i <;> simp [matVec, momentumMatrix, rawPre]

theorem momentumMatrix_eq_actual_derivative (y : ℝ) :
    WithLp.toLp 2 (matVec momentumMatrix (rawPre y)) =
      (-Complex.I) • deriv pre y := by
  rw [matVec_momentumMatrix, ← momentum_eq_actual_derivative, momentum_eq]

theorem weakDenominator_eq (d r y : ℝ) :
    weakDenominator (rawPre y) (rawPost d r y) = (d : ℂ) := by
  rw [weakDenominator, cinner_eq_inner]
  exact overlap_eq d r y

theorem weakNumerator_eq (d r y : ℝ) :
    weakNumerator momentumMatrix (rawPre y) (rawPost d r y) = (r : ℂ) := by
  rw [weakNumerator, matVec_momentumMatrix, cinner_eq_inner]
  simpa only [momentum_eq] using numerator_eq d r y

theorem guarded_readout {d : ℝ} (hd : d ≠ 0) (r y : ℝ) :
    weakValue? momentumMatrix (rawPre y) (rawPost d r y) = some ((r / d : ℝ) : ℂ) := by
  simp [weakValue?, weakDenominator_eq, weakNumerator_eq,
    Complex.ofReal_ne_zero.mpr hd, Complex.ofReal_div]

theorem guarded_readout_at_zero (r y : ℝ) :
    weakValue? momentumMatrix (rawPre y) (rawPost 0 r y) = none := by
  simp [weakValue?, weakDenominator_eq]

theorem contDiff_pre : ContDiff ℝ ∞ pre := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · simpa [pre, rawPre] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℂ)))
  · have h : ContDiff ℝ ∞ (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
    simpa [pre, rawPre, phase] using (h.mul (contDiff_const (c := Complex.I))).cexp

/-- The postselected state is jointly smooth even on the zero-overlap plane. -/
theorem contDiff_post :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => post q.1 q.2.1 q.2.2) := by
  have hd : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (q.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have hr : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (q.2.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)
  have hy : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (q.2.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · simpa [post, rawPost, Complex.ofReal_sub] using hd.sub hr
  · simpa [post, rawPost, phase] using hr.mul ((hy.mul contDiff_const).cexp)

end InfoGeometry.Canonical.TwoStateMomentumShear
