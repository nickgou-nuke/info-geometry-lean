import InfoGeometry.Inference.PoissonBregman
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Positive-domain topology for the Poisson Bregman term

The scalar Poisson Bregman expression contains a logarithmic quotient.  On
strictly positive observations and means it is continuous; the zero-observation
branch is intentionally left to its separate algebraic theorem.
-/

namespace InfoGeometry.Inference

abbrev PositiveReal := {x : ℝ // 0 < x}

noncomputable def poissonBregmanPositive :
    PositiveReal × PositiveReal → ℝ :=
  fun p => poissonBregman p.1.1 p.2.1

theorem continuous_poissonBregmanPositive :
    Continuous poissonBregmanPositive := by
  have hy : Continuous (fun p : PositiveReal × PositiveReal => p.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hlam : Continuous (fun p : PositiveReal × PositiveReal => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hratio : Continuous
      (fun p : PositiveReal × PositiveReal => p.1.1 / p.2.1) :=
    hy.div hlam (fun p => p.2.property.ne')
  have hlog : Continuous
      (fun p : PositiveReal × PositiveReal =>
        Real.log (p.1.1 / p.2.1)) :=
    hratio.log (fun p => div_ne_zero p.1.property.ne' p.2.property.ne')
  have hformula :
      poissonBregmanPositive =
        (fun p : PositiveReal × PositiveReal =>
          p.1.1 * Real.log (p.1.1 / p.2.1) - (p.1.1 - p.2.1)) := by
    funext p
    unfold poissonBregmanPositive poissonBregman
    rw [if_neg p.1.property.ne']
  rw [hformula]
  exact (hy.mul hlog).sub (hy.sub hlam)

theorem poissonBregmanPositive_nonneg
    (p : PositiveReal × PositiveReal) :
    0 ≤ poissonBregmanPositive p := by
  exact poissonBregman_nonneg p.1.property.le p.2.property

end InfoGeometry.Inference
