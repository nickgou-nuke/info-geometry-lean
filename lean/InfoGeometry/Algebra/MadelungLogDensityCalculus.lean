import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace InfoGeometry.Algebra.MadelungLogDensityCalculus

noncomputable section

def positiveAmplitude (logDensity : ℝ → ℝ) (point : ℝ) : ℝ :=
  Real.exp (logDensity point / 2)

theorem positiveAmplitude_pos (logDensity : ℝ → ℝ) (point : ℝ) :
    0 < positiveAmplitude logDensity point := Real.exp_pos _

theorem positiveAmplitude_sq (logDensity : ℝ → ℝ) (point : ℝ) :
    positiveAmplitude logDensity point ^ 2 = Real.exp (logDensity point) := by
  rw [positiveAmplitude, sq, ← Real.exp_add]
  congr 1
  ring

theorem hasDerivAt_positiveAmplitude
    (logDensity : ℝ → ℝ) (point : ℝ)
    (differentiable : DifferentiableAt ℝ logDensity point) :
    HasDerivAt (positiveAmplitude logDensity)
      (positiveAmplitude logDensity point * (deriv logDensity point / 2)) point := by
  exact (differentiable.hasDerivAt.div_const 2).exp

theorem deriv_positiveAmplitude (logDensity : ℝ → ℝ)
    (differentiable : Differentiable ℝ logDensity) :
    deriv (positiveAmplitude logDensity) =
      fun point => positiveAmplitude logDensity point * (deriv logDensity point / 2) := by
  funext point
  exact (hasDerivAt_positiveAmplitude logDensity point (differentiable point)).deriv

theorem curvature_eq_log_density (logDensity : ℝ → ℝ) (point : ℝ)
    (differentiable : Differentiable ℝ logDensity)
    (twice_differentiable : DifferentiableAt ℝ (deriv logDensity) point) :
    deriv (deriv (positiveAmplitude logDensity)) point /
        positiveAmplitude logDensity point =
      deriv (deriv logDensity) point / 2 + (deriv logDensity point) ^ 2 / 4 := by
  rw [deriv_positiveAmplitude logDensity differentiable]
  have second :
      deriv (fun location =>
        positiveAmplitude logDensity location * (deriv logDensity location / 2)) point =
        (positiveAmplitude logDensity point * (deriv logDensity point / 2)) *
            (deriv logDensity point / 2) +
          positiveAmplitude logDensity point * (deriv (deriv logDensity) point / 2) := by
    change deriv ((fun location => Real.exp (logDensity location / 2)) *
      (fun location => deriv logDensity location / 2)) point = _
    rw [deriv_mul
      (((differentiable point).div_const 2).exp)
      (twice_differentiable.div_const 2)]
    dsimp only [positiveAmplitude]
    rw [((differentiable point).div_const 2).hasDerivAt.exp.deriv]
    rw [deriv_div_const (c := logDensity) (d := (2 : ℝ))]
    rw [(differentiable point).hasDerivAt.deriv]
    rw [deriv_div_const (c := deriv logDensity) (d := (2 : ℝ))]
  rw [second]
  have amplitude_ne := ne_of_gt (positiveAmplitude_pos logDensity point)
  field_simp
  ring

theorem sqrt_density_eq_positiveAmplitude (density : ℝ → ℝ)
    (positive : ∀ point, 0 < density point) :
    (fun point => Real.sqrt (density point)) =
      positiveAmplitude (fun point => Real.log (density point)) := by
  funext point
  rw [positiveAmplitude, Real.exp_half, Real.exp_log (positive point)]

theorem sqrt_density_curvature (density : ℝ → ℝ) (point : ℝ)
    (positive : ∀ point, 0 < density point)
    (differentiable : Differentiable ℝ density)
    (twice_log_differentiable :
      DifferentiableAt ℝ (deriv (fun location => Real.log (density location))) point) :
    deriv (deriv (fun location => Real.sqrt (density location))) point /
        Real.sqrt (density point) =
      deriv (deriv (fun location => Real.log (density location))) point / 2 +
        (deriv (fun location => Real.log (density location)) point) ^ 2 / 4 := by
  have log_differentiable : Differentiable ℝ (fun location => Real.log (density location)) :=
    fun location => (differentiable location).log (ne_of_gt (positive location))
  have amplitude_eq := sqrt_density_eq_positiveAmplitude density positive
  have value_eq := congrFun amplitude_eq point
  rw [amplitude_eq, value_eq]
  exact curvature_eq_log_density _ point log_differentiable twice_log_differentiable

end

end InfoGeometry.Algebra.MadelungLogDensityCalculus
