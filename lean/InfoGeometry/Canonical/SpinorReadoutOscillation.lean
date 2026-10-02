import InfoGeometry.Canonical.SpinorHydrodynamicReadout
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Constant-density spinors with unbounded readout derivatives

The spatial field is `(cos (N*x+π/4), sin (N*x+π/4) * exp (I*y))`.
Its actual derivative in the second spatial coordinate supplies the current
used by `SpinorHydrodynamicReadout`. The reconstructed second velocity
component is uniformly bounded, while its first spatial derivative at the
origin is `kappa*N`.

This is a family of smooth local configurations, not a singular evolution.
No Navier--Stokes equation or matrix-barrier estimate is assumed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.SpinorReadoutOscillation

open scoped InnerProductSpace
open SpinorHydrodynamicReadout

abbrev Spinor := EuclideanSpace ℂ (Fin 2)

def spinor (N x y : ℝ) : Spinor :=
  !₂[(Real.cos (N * x + Real.pi / 4) : ℂ),
    (Real.sin (N * x + Real.pi / 4) : ℂ) * Complex.exp ((y : ℂ) * Complex.I)]

/-- The derivative in the second spatial coordinate at `y = 0`. -/
def yDerivative (N x : ℝ) : Spinor :=
  !₂[0, (Real.sin (N * x + Real.pi / 4) : ℂ) * Complex.I]

theorem density_spinor (N x y : ℝ) : density (spinor N x y) = 1 := by
  simp only [density, EuclideanSpace.norm_sq_eq, spinor, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, norm_mul, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq (N * x + Real.pi / 4)]

theorem spinor_ne_zero (N x y : ℝ) : spinor N x y ≠ 0 := by
  apply (density_pos_iff _).mp
  rw [density_spinor]
  norm_num

theorem hasDerivAt_spinor_y (N x : ℝ) :
    HasDerivAt (spinor N x) (yDerivative N x) 0 := by
  have hexp : HasDerivAt (fun y : ℝ => Complex.exp ((y : ℂ) * Complex.I))
      Complex.I 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp)
  have hp : HasDerivAt
      (fun y : ℝ => ![(Real.cos (N * x + Real.pi / 4) : ℂ),
        (Real.sin (N * x + Real.pi / 4) : ℂ) * Complex.exp ((y : ℂ) * Complex.I)])
      (![0, (Real.sin (N * x + Real.pi / 4) : ℂ) * Complex.I]) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hasDerivAt_const (0 : ℝ) (Real.cos (N * x + Real.pi / 4) : ℂ)
    · simpa using hexp.const_mul (Real.sin (N * x + Real.pi / 4) : ℂ)
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt 0 hp

/-- The second velocity component, reconstructed from the actual spatial jet. -/
def velocityComponent (kappa N x : ℝ) : ℝ :=
  readout kappa (spinor N x 0) (yDerivative N x)

theorem velocityComponent_eq (kappa N x : ℝ) :
    velocityComponent kappa N x = kappa * Real.sin (N * x + Real.pi / 4) ^ 2 := by
  rw [velocityComponent, readout, density_spinor]
  have hs (c s : ℝ) : current kappa (!₂[(c : ℂ), (s : ℂ)] : Spinor)
      !₂[0, (s : ℂ) * Complex.I] = kappa * s ^ 2 := by
    simp [current, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
      Complex.mul_im, pow_two]
  simpa only [spinor, yDerivative, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one, div_one] using hs (Real.cos (N*x+Real.pi/4)) (Real.sin (N*x+Real.pi/4))

theorem velocityComponent_nonneg {kappa : ℝ} (hk : 0 ≤ kappa) (N x : ℝ) :
    0 ≤ velocityComponent kappa N x := by
  rw [velocityComponent_eq]
  exact mul_nonneg hk (sq_nonneg _)

theorem abs_velocityComponent_le {kappa : ℝ} (hk : 0 ≤ kappa) (N x : ℝ) :
    |velocityComponent kappa N x| ≤ kappa := by
  rw [abs_of_nonneg (velocityComponent_nonneg hk N x), velocityComponent_eq]
  have hs : Real.sin (N * x + Real.pi / 4) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (N * x + Real.pi / 4),
      sq_nonneg (Real.cos (N * x + Real.pi / 4))]
  simpa using mul_le_mul_of_nonneg_left hs hk

theorem hasDerivAt_velocityComponent (kappa N x : ℝ) :
    HasDerivAt (velocityComponent kappa N)
      (kappa * N * Real.sin (2 * (N * x + Real.pi / 4))) x := by
  have hs := (((hasDerivAt_id x).const_mul N).add_const (Real.pi / 4)).sin
  have h := (hs.pow 2).const_mul kappa
  convert h using 1
  · funext r
    exact velocityComponent_eq kappa N r
  · simp only [Real.sin_two_mul, id_eq]
    ring

theorem hasDerivAt_velocityComponent_zero (kappa N : ℝ) :
    HasDerivAt (velocityComponent kappa N) (kappa * N) 0 := by
  have h := hasDerivAt_velocityComponent kappa N 0
  have hangle : 2 * (N * 0 + Real.pi / 4) = Real.pi / 2 := by ring
  simpa only [hangle, Real.sin_pi_div_two, mul_one] using h

theorem deriv_velocityComponent_zero (kappa N : ℝ) :
    deriv (velocityComponent kappa N) 0 = kappa * N :=
  (hasDerivAt_velocityComponent_zero kappa N).deriv

/-- Unit density and uniformly bounded velocity do not bound the spatial
derivative of this explicitly reconstructed family. -/
theorem exists_arbitrarily_large_readout_derivative {kappa : ℝ} (hk : 0 < kappa)
    (C : ℝ) :
    ∃ N : ℕ,
      (∀ x y : ℝ, density (spinor N x y) = 1) ∧
      (∀ x : ℝ, |velocityComponent kappa N x| ≤ kappa) ∧
      C < deriv (velocityComponent kappa N) 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (C / kappa)
  refine ⟨N, density_spinor N, abs_velocityComponent_le hk.le N, ?_⟩
  rw [deriv_velocityComponent_zero]
  simpa [mul_comm] using (div_lt_iff₀ hk).mp hN

end InfoGeometry.Canonical.SpinorReadoutOscillation
