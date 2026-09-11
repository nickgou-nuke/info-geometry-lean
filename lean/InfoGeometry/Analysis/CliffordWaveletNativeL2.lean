import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Native L2 owners for Clifford-valued wavelet analysis

The coefficient space is an arbitrary complex Hilbert space.  In particular,
this applies to finite-dimensional Hilbert realizations of a Clifford algebra;
no commutativity of coefficient multiplication is used.

The statements are direct specializations of Mathlib's vector-valued Schwartz
Fourier theory.  They provide the analytic owner layer needed before proving a
Clifford-wavelet Heisenberg or Donoho--Stark inequality.
-/

noncomputable section

namespace InfoGeometry.Analysis.CliffordWaveletNativeL2

open MeasureTheory

variable
    {V : Type*}
    [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [MeasurableSpace V]
    [BorelSpace V]
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    [CompleteSpace H]

/-- Vector-valued Plancherel identity on Schwartz signals. -/
theorem integral_normSq_fourier (f : SchwartzMap V H) :
    ∫ ξ : V, ‖(FourierTransform.fourier f) ξ‖ ^ 2 =
      ∫ x : V, ‖f x‖ ^ 2 :=
  SchwartzMap.integral_norm_sq_fourier f

/-- The Fourier transform preserves the native `L2` norm. -/
theorem norm_fourier_toL2_eq (f : SchwartzMap V H) :
    ‖(FourierTransform.fourier f).toLp 2 volume‖ =
      ‖f.toLp 2 volume‖ :=
  SchwartzMap.norm_fourier_toL2_eq f

/--
Native Cauchy--Schwarz product inequality.  This is the Hilbert-space owner
from which Robertson/Heisenberg variance bounds are derived after identifying
the relevant centered operator vectors.
-/
theorem inner_product_uncertainty_bound (x y : H) :
    ‖inner ℂ x y‖ * ‖inner ℂ y x‖ ≤
      RCLike.re (inner ℂ x x) * RCLike.re (inner ℂ y y) :=
  inner_mul_inner_self_le x y

/--
The Robertson uncertainty estimate before choosing any concrete observables:
the antisymmetric (imaginary) component of the Hilbert pairing is bounded by
the product of the two fluctuation norms.

For centered operator vectors `x = (A - ⟨A⟩) ψ` and
`y = (B - ⟨B⟩) ψ`, the left side is the commutator expectation up to the
standard factor of two.  No commutativity or diagonalization hypothesis is
used.
-/
theorem imaginary_inner_uncertainty_bound (x y : H) :
    |RCLike.im (inner ℂ x y)| ≤ ‖x‖ * ‖y‖ :=
  (RCLike.abs_im_le_norm (inner ℂ x y)).trans (norm_inner_le_norm x y)

/-- The fluctuation vector of a bounded operator in a chosen state. -/
def centeredOperatorVector (A : H →L[ℂ] H) (ψ : H) : H :=
  A ψ - inner ℂ ψ (A ψ) • ψ

/--
The standard-deviation norm before scalar squaring or expectation packaging.
It remains an operator/state construction on the full noncommutative carrier.
-/
def operatorDeviation (A : H →L[ℂ] H) (ψ : H) : ℝ :=
  ‖centeredOperatorVector A ψ‖

/--
Native bounded-operator uncertainty theorem.  It applies Cauchy--Schwarz to
the two centered operator vectors and therefore does not assume simultaneous
diagonalizability or commutativity of the observables.
-/
theorem centered_operator_uncertainty
    (A B : H →L[ℂ] H) (ψ : H) :
    |RCLike.im
        (inner ℂ (centeredOperatorVector A ψ)
          (centeredOperatorVector B ψ))| ≤
      operatorDeviation A ψ * operatorDeviation B ψ :=
  imaginary_inner_uncertainty_bound
    (centeredOperatorVector A ψ) (centeredOperatorVector B ψ)

/--
Fourier transform converts a directional derivative into multiplication by
the corresponding frequency coordinate.
-/
theorem fourier_lineDeriv_eq_frequencyMultiplication
    (f : SchwartzMap V H) (m : V) :
    FourierTransform.fourier (LineDeriv.lineDerivOp m f) =
      (2 * (Real.pi : ℂ) * Complex.I) •
        (SchwartzMap.smulLeftCLM H (fun x => inner ℝ x m))
          (FourierTransform.fourier f) :=
  SchwartzMap.fourier_lineDerivOp_eq f m

/--
Directional differentiation of the Fourier transform is Fourier transform of
coordinate multiplication on the original signal.
-/
theorem lineDeriv_fourier_eq_frequencyMoment
    (f : SchwartzMap V H) (m : V) :
    LineDeriv.lineDerivOp m (FourierTransform.fourier f) =
      FourierTransform.fourier
        (-(2 * (Real.pi : ℂ) * Complex.I) •
          (SchwartzMap.smulLeftCLM H (fun x => inner ℝ x m)) f) :=
  SchwartzMap.lineDerivOp_fourier_eq f m

section NoncommutativeCoefficients

variable
    {D : Type*}
    [NormedAddCommGroup D]
    [NormedSpace ℝ D]
    [MeasurableSpace D]
    [BorelSpace D]
    [FiniteDimensional ℝ D]
    {μ : Measure D}
    [μ.IsAddHaarMeasure]
    {A : Type*}
    [NormedRing A]
    [NormedSpace ℝ A]
    [IsScalarTower ℝ A A]
    [SMulCommClass ℝ A A]

/--
Schwartz integration by parts with coefficients in a possibly
noncommutative normed ring.
-/
theorem integral_mul_lineDeriv_right_eq_neg_left
    (f g : SchwartzMap D A) (v : D) :
    ∫ x : D, f x * (LineDeriv.lineDerivOp v g) x ∂μ =
      -∫ x : D, (LineDeriv.lineDerivOp v f) x * g x ∂μ :=
  SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left f g v

end NoncommutativeCoefficients

end InfoGeometry.Analysis.CliffordWaveletNativeL2
