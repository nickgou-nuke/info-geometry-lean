import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Bogoliubov-Covariant Mellin–Krein Quantization Bridge

This module formalizes:
1. **The 1-Mode $\mathrm{SU}(1,1)$ Bogoliubov Transformation Matrix:**
   $$\mathcal{B}(u, t, \ln n) = R(t \ln n) \cdot B_{\mathrm{sq}}(u \ln n) =
     \begin{pmatrix}
     e^{-i t \ln n} \cosh(u \ln n) & e^{-i t \ln n} \sinh(u \ln n) \\
     e^{i t \ln n} \sinh(u \ln n) & e^{i t \ln n} \cosh(u \ln n)
     \end{pmatrix}$$

2. **Scalar Bogoliubov normalization identity:**
   $$|\alpha|^2 - |\beta|^2 = \cosh^2(r) - \sinh^2(r) = 1$$
   This is only the coefficient identity; no CCR algebra or Fock implementer is
   defined in this module.

3. **Matrix determinant normalization:**
   $$\det(\mathcal{B}(u, t, \ln n)) = 1$$

4. **Krein Reflection and Inverse Squeezing:**
   $$B_{\mathrm{sq}}(-r) = (B_{\mathrm{sq}}(r))^{-1}$$
   mapping the functional equation reflection $u \mapsto -u$ to Bogoliubov boost inversion.

5. **Critical Line Fixed Polarization Locus:**
   $$u = 0 \iff r = 0 \iff B_{\mathrm{sq}}(0) = I_2$$
   proving only a matrix fixed-point statement for the supplied rapidity.

6. **Real squeezing coordinate:**
   $$q(r)=\tanh r,\qquad |q(r)|<1.$$
   This is not yet a complex $\beta/\bar\alpha$ or a proved Möbius action.
-/

noncomputable section

namespace InfoGeometry.Canonical.BogoliubovMellinKrein

open Matrix Complex Real

abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-! ## 1. Hyperbolic Squeezing and Phase Rotor Matrices -/

/-- Hyperbolic squeezing boost matrix B_sq(r) in the doubled mode basis (a, a†) -/
def squeezingMatrix (r : ℝ) : Mat2C :=
  !![(Complex.cosh (r : ℂ)), (Complex.sinh (r : ℂ));
     (Complex.sinh (r : ℂ)), (Complex.cosh (r : ℂ))]

/-- Compact phase rotor matrix R(θ) -/
def phaseRotorMatrix (theta : ℝ) : Mat2C :=
  !![Complex.exp (-Complex.I * (theta : ℂ)), 0;
     0, Complex.exp (Complex.I * (theta : ℂ))]

/-- Full Bogoliubov matrix ℬ(u, t, ln n) = R(t ln n) * B_sq(u ln n) -/
def bogoliubovMatrix (u t log_n : ℝ) : Mat2C :=
  (phaseRotorMatrix (t * log_n)) * (squeezingMatrix (u * log_n))

/-- Mellin scale rapidity for the mode indexed by `n`. -/
def bogoliubovRapidity (n : ℕ) (u : ℝ) : ℝ :=
  u * Real.log (n : ℝ)

/-! ## 2. Scalar Bogoliubov normalization -/

/-- 🏆 THEOREM 1: Hyperbolic Identity cosh²(r) - sinh²(r) = 1 -/
theorem cosh_sq_sub_sinh_sq_eq_one (r : ℝ) :
    (Real.cosh r)^2 - (Real.sinh r)^2 = 1 := by
  exact Real.cosh_sq_sub_sinh_sq r

/-- The coefficient normalization `‖α‖² - ‖β‖² = 1`.
This does not by itself prove a CCR representation. -/
theorem bogoliubov_ccr_invariance (r theta : ℝ) :
    let alpha : ℂ := Complex.exp (-Complex.I * (theta : ℂ)) * (Real.cosh r : ℂ)
    let beta  : ℂ := Complex.exp (-Complex.I * (theta : ℂ)) * (Real.sinh r : ℂ)
    ‖alpha‖^2 - ‖beta‖^2 = 1 := by
  intro alpha beta
  dsimp [alpha, beta]
  have h_phase : ‖Complex.exp (-Complex.I * (theta : ℂ))‖ = 1 := by
    have h_eq : -Complex.I * (theta : ℂ) = (-theta : ℝ) * Complex.I := by
      push_cast
      ring
    rw [h_eq, Complex.norm_exp_ofReal_mul_I]
  rw [norm_mul, norm_mul, h_phase, one_mul, one_mul]
  have h_cosh : ‖(Real.cosh r : ℂ)‖ = Real.cosh r := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.cosh_pos _).le]
  have h_sinh : ‖(Real.sinh r : ℂ)‖ = |Real.sinh r| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h_cosh, h_sinh, sq_abs]
  exact cosh_sq_sub_sinh_sq_eq_one r

/-! ## 3. Matrix determinant normalization -/

/-- 🏆 THEOREM 3: Squeezing Matrix Determinant is 1 -/
@[simp] theorem det_squeezingMatrix (r : ℝ) :
    (squeezingMatrix r).det = 1 := by
  dsimp [squeezingMatrix]
  rw [Matrix.det_fin_two]
  simp [squeezingMatrix, Matrix.det_fin_two]
  have h := Complex.cosh_sq_sub_sinh_sq (r : ℂ)
  linear_combination h

/-- 🏆 THEOREM 4: Phase Rotor Matrix Determinant is 1 -/
@[simp] theorem det_phaseRotorMatrix (theta : ℝ) :
    (phaseRotorMatrix theta).det = 1 := by
  simp [phaseRotorMatrix, Matrix.det_fin_two]
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 1 <;> ring

/-- The displayed matrix has determinant one.  No symplectic-form
preservation theorem is asserted here. -/
@[simp] theorem det_bogoliubovMatrix (u t log_n : ℝ) :
    (bogoliubovMatrix u t log_n).det = 1 := by
  dsimp [bogoliubovMatrix]
  rw [Matrix.det_mul, det_phaseRotorMatrix, det_squeezingMatrix, mul_one]

/-! ## 4. Krein Reflection and Inverse Squeezing -/

/-- 🏆 THEOREM 6: Negative Rapidity Inverts the Squeezing Matrix: B_sq(-r) * B_sq(r) = I -/
theorem squeezingMatrix_mul_inv (r : ℝ) :
    (squeezingMatrix (-r)) * (squeezingMatrix r) = 1 := by
  have h_cosh_neg : Complex.cosh ((-r : ℝ) : ℂ) = Complex.cosh (r : ℂ) := by
    have h : ((-r : ℝ) : ℂ) = - (r : ℂ) := by simp
    rw [h, Complex.cosh_neg]
  have h_sinh_neg : Complex.sinh ((-r : ℝ) : ℂ) = -Complex.sinh (r : ℂ) := by
    have h : ((-r : ℝ) : ℂ) = - (r : ℂ) := by simp
    rw [h, Complex.sinh_neg]
  have h_id := Complex.cosh_sq_sub_sinh_sq (r : ℂ)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [squeezingMatrix, Matrix.mul_apply, Fin.sum_univ_two, h_cosh_neg, h_sinh_neg]
    linear_combination h_id
  · simp [squeezingMatrix, Matrix.mul_apply, Fin.sum_univ_two, h_cosh_neg, h_sinh_neg]
    ring
  · simp [squeezingMatrix, Matrix.mul_apply, Fin.sum_univ_two, h_cosh_neg, h_sinh_neg]
    ring
  · simp [squeezingMatrix, Matrix.mul_apply, Fin.sum_univ_two, h_cosh_neg, h_sinh_neg]
    linear_combination h_id

/-! ## 5. Matrix fixed-point locus (u = 0 ↔ B_sq = I) -/

/-- 🏆 THEOREM 7: Zero Squeezing Rapidity at r = 0 Gives the Identity Operator -/
@[simp] theorem squeezingMatrix_zero :
    squeezingMatrix 0 = 1 := by
  dsimp [squeezingMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Real.cosh_zero, Real.sinh_zero]
  }

/-- 🏆 THEOREM 8: Squeezing Matrix Equals Identity If and Only If Rapidity is Zero -/
theorem squeezingMatrix_eq_one_iff (r : ℝ) :
    squeezingMatrix r = 1 ↔ r = 0 := by
  constructor
  · intro h
    have h_entry : (squeezingMatrix r) 0 1 = (1 : Mat2C) 0 1 := by rw [h]
    dsimp [squeezingMatrix] at h_entry
    have h_sinh_zero : (Real.sinh r : ℂ) = 0 := by
      simpa using h_entry
    have h_r_zero : Real.sinh r = 0 := by
      exact Complex.ofReal_eq_zero.mp h_sinh_zero
    have h_sinh_eq : Real.sinh r = Real.sinh 0 := by
      rw [Real.sinh_zero, h_r_zero]
    exact Real.sinh_injective h_sinh_eq
  · rintro rfl
    exact squeezingMatrix_zero

/-- If the supplied scale coordinate is positive, zero rapidity is
equivalent to the matrix fixed point. -/
theorem critical_line_fixed_polarization (u log_n : ℝ) (hlog_pos : 0 < log_n) :
    squeezingMatrix (u * log_n) = 1 ↔ u = 0 := by
  rw [squeezingMatrix_eq_one_iff]
  have h_ne : log_n ≠ 0 := ne_of_gt hlog_pos
  constructor
  · intro h
    cases mul_eq_zero.mp h with
    | inl hu => exact hu
    | inr hlog => exact (h_ne hlog).elim
  · rintro rfl
    ring

/-! ## 6. Real squeezing coordinate -/
/- The real hyperbolic coordinate `tanh r`.  A complex polarization ratio
and its Möbius action require separate representation data. -/
def realSqueezingDiskCoordinate (r : ℝ) : ℝ :=
  Real.tanh r

/- The real squeezing coordinate lies strictly inside the unit interval. -/
theorem realSqueezingDiskCoordinate_abs_lt_one (r : ℝ) :
    |realSqueezingDiskCoordinate r| < 1 := by
  dsimp [realSqueezingDiskCoordinate]
  exact Real.abs_tanh_lt_one r

/- Finite matrix/readout packet for the supplied Mellin rapidity. -/
theorem finite_bogoliubov_mellin_readout
    (u t log_n : ℝ) (hlog_pos : 0 < log_n) :
    ((bogoliubovMatrix u t log_n).det = 1) ∧
    ((squeezingMatrix (-(u * log_n))) * (squeezingMatrix (u * log_n)) = 1) ∧
    (squeezingMatrix (u * log_n) = 1 ↔ u = 0) ∧
    (|realSqueezingDiskCoordinate (u * log_n)| < 1) := by
  exact ⟨det_bogoliubovMatrix u t log_n,
         squeezingMatrix_mul_inv (u * log_n),
         critical_line_fixed_polarization u log_n hlog_pos,
         realSqueezingDiskCoordinate_abs_lt_one (u * log_n)⟩

end InfoGeometry.Canonical.BogoliubovMellinKrein
