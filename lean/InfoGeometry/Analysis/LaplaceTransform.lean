import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# InfoGeometry.Analysis.LaplaceTransform

Native Laplace transform core, modeled after the repo's Fourier and Mellin
implementation style.

This file does not replicate AFP theorem names.  It keeps the transform
definition, a convergence predicate, and the basic algebraic laws that are
stable in Lean's kernel:

* zero;
* additivity;
* scalar multiplication.

The analytic inversion / uniqueness / contour theory remains separate and is
not claimed here.
-/

noncomputable section

namespace InfoGeometry.Analysis.LaplaceTransform

open scoped BigOperators

/--
Laplace kernel on the real line.

We use the complex exponential kernel `exp (-s * t)` with `t : ℝ` coerced to
`ℂ`.  This is the native analytic core behind the classical Laplace transform.
-/
def laplaceKernel (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(s * (t : ℂ)))

/--
Laplace transform with respect to an arbitrary measure on `ℝ`.

This keeps the analytic carrier explicit, just as the Fourier transform API
does in mathlib.
-/
def laplaceIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : MeasureTheory.Measure ℝ) (f : ℝ → E) (s : ℂ) : E :=
  ∫ t, laplaceKernel s t • f t ∂μ

/--
Default Laplace transform on Lebesgue measure.

This is the standard transform form used by downstream packets when no
alternative carrier measure is needed.
-/
def laplaceTransform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) : E :=
  laplaceIntegral MeasureTheory.volume f s

/--
Integrability predicate for the Laplace transform.

The transform is only mathematically meaningful under this convergence
condition; the definition itself remains total.
-/
def LaplaceConvergent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : MeasureTheory.Measure ℝ) (f : ℝ → E) (s : ℂ) : Prop :=
  MeasureTheory.Integrable (fun t => laplaceKernel s t • f t) μ

/--
The Laplace transform over the positive half-line `Ioi 0`.

This is the classical carrier for Laplace analysis and supports the clean
scaling law under positive dilation.
-/
def laplaceIntegralPos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) : E :=
  ∫ t in Set.Ioi (0 : ℝ), laplaceKernel s t • f t

/-- Standard Laplace transform over the positive half-line. -/
def laplaceTransformPos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) : E :=
  laplaceIntegralPos f s

/-- Convergence predicate for the classical positive-half-line Laplace transform. -/
def LaplaceConvergentPos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) : Prop :=
  MeasureTheory.IntegrableOn (fun t => laplaceKernel s t • f t) (Set.Ioi (0 : ℝ))

/-- Spectral shift law for the Laplace kernel. -/
theorem laplaceKernel_add (s c : ℂ) (t : ℝ) :
    laplaceKernel (s + c) t = Complex.exp (-(c * (t : ℂ))) * laplaceKernel s t := by
  calc
    laplaceKernel (s + c) t = Complex.exp (-((s + c) * (t : ℂ))) := rfl
    _ = Complex.exp (-(c * (t : ℂ)) + -(s * (t : ℂ))) := by
          congr 1
          ring
    _ = Complex.exp (-(c * (t : ℂ))) * Complex.exp (-(s * (t : ℂ))) := by
          rw [Complex.exp_add]
    _ = Complex.exp (-(c * (t : ℂ))) * laplaceKernel s t := by rfl

/-- Time-variable scaling law for the Laplace kernel. -/
theorem laplaceKernel_mul (s : ℂ) (a : ℝ) (t : ℝ) :
    laplaceKernel s (a * t) = laplaceKernel (s * (a : ℂ)) t := by
  have h :
      (↑(a * t) : ℂ) = (a : ℂ) * (t : ℂ) := by
    simp
  rw [laplaceKernel, laplaceKernel, h, mul_assoc]

/-- The Laplace kernel is jointly continuous in the spectral and time variables. -/
theorem continuous_laplaceKernel :
    Continuous fun p : ℂ × ℝ => laplaceKernel p.1 p.2 := by
  continuity

namespace laplaceIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {μ : MeasureTheory.Measure ℝ}

/-- The Laplace transform of the zero function is zero. -/
theorem zero_integral (s : ℂ) :
    laplaceIntegral μ (fun _ : ℝ => (0 : E)) s = 0 := by
  simp [laplaceIntegral]

/-- Laplace transform is additive on convergent inputs. -/
theorem add {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent μ f s) (hg : LaplaceConvergent μ g s) :
    laplaceIntegral μ (fun t => f t + g t) s =
      laplaceIntegral μ f s + laplaceIntegral μ g s := by
  change ∫ t, laplaceKernel s t • (f t + g t) ∂μ =
    laplaceIntegral μ f s + laplaceIntegral μ g s
  simpa [smul_add] using
    (MeasureTheory.integral_add hf hg)

/-- Laplace transform is homogeneous on convergent inputs. -/
theorem smul (c : ℂ) {f : ℝ → E} {s : ℂ}
    :
    laplaceIntegral μ (fun t => c • f t) s = c • laplaceIntegral μ f s := by
  change ∫ t, laplaceKernel s t • (c • f t) ∂μ = c • laplaceIntegral μ f s
  calc
    ∫ t, laplaceKernel s t • (c • f t) ∂μ
        = ∫ t, c • (laplaceKernel s t • f t) ∂μ := by
            congr with t
            exact smul_comm (laplaceKernel s t) c (f t)
    _ = c • ∫ t, laplaceKernel s t • f t ∂μ := by
          exact MeasureTheory.integral_smul c (fun t => laplaceKernel s t • f t)

/-- Laplace transform is closed under negation on convergent inputs. -/
theorem neg {f : ℝ → E} {s : ℂ}
    :
    laplaceIntegral μ (fun t => - f t) s = - laplaceIntegral μ f s := by
  simpa using (laplaceIntegral.smul (μ := μ) (c := (-1 : ℂ)) (f := f) (s := s))

/-- Laplace transform is closed under subtraction on convergent inputs. -/
theorem sub {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent μ f s) (hg : LaplaceConvergent μ g s) :
    laplaceIntegral μ (fun t => f t - g t) s =
      laplaceIntegral μ f s - laplaceIntegral μ g s := by
  change ∫ t, laplaceKernel s t • (f t - g t) ∂μ =
    laplaceIntegral μ f s - laplaceIntegral μ g s
  simpa [smul_sub] using (MeasureTheory.integral_sub hf hg)

/-- Convergence is preserved by addition. -/
theorem convergent_add {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent μ f s) (hg : LaplaceConvergent μ g s) :
    LaplaceConvergent μ (fun t => f t + g t) s := by
  simpa [LaplaceConvergent, smul_add] using hf.add hg

/-- Convergence is preserved by scalar multiplication. -/
theorem convergent_smul (c : ℂ) {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent μ f s) :
    LaplaceConvergent μ (fun t => c • f t) s := by
  have h : MeasureTheory.Integrable (fun t => c • (laplaceKernel s t • f t)) μ :=
    MeasureTheory.Integrable.smul c hf
  change MeasureTheory.Integrable (fun t => laplaceKernel s t • (c • f t)) μ
  convert h using 1
  · funext t
    exact smul_comm (laplaceKernel s t) c (f t)

/-- Spectral shift for the Laplace transform. -/
theorem add_spectral {f : ℝ → E} {s c : ℂ} :
    laplaceIntegral μ f (s + c) =
      laplaceIntegral μ (fun t => Complex.exp (-(c * (t : ℂ))) • f t) s := by
  rw [laplaceIntegral, laplaceIntegral]
  congr with t
  calc
    laplaceKernel (s + c) t • f t
        = (Complex.exp (-(c * (t : ℂ))) * laplaceKernel s t) • f t := by
            rw [laplaceKernel_add]
    _ = Complex.exp (-(c * (t : ℂ))) • (laplaceKernel s t • f t) := by
          rw [mul_smul]
    _ = laplaceKernel s t • (Complex.exp (-(c * (t : ℂ))) • f t) := by
          rw [smul_comm]

/-- Frequency shift for the Laplace transform on convergent inputs. -/
theorem frequency_shift {f : ℝ → E} {s b : ℂ}
    :
    laplaceIntegral μ (fun t => Complex.exp (b * (t : ℂ)) • f t) s =
      laplaceIntegral μ f (s - b) := by
  rw [sub_eq_add_neg]
  simpa [laplaceKernel, mul_add, add_comm, add_left_comm, add_assoc] using
    (add_spectral (μ := μ) (E := E) (f := f) (s := s) (c := -b)).symm

end laplaceIntegral

namespace LaplaceConvergent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {μ : MeasureTheory.Measure ℝ}

/-- The zero function is Laplace-convergent. -/
theorem zero (s : ℂ) :
    LaplaceConvergent μ (fun _ : ℝ => (0 : E)) s := by
  have h0 : MeasureTheory.Integrable (fun _ : ℝ => (0 : E)) μ := by
    simpa using (MeasureTheory.integrable_zero (μ := μ))
  simpa [LaplaceConvergent, laplaceKernel] using h0

/-- Convergence is preserved by addition. -/
theorem add {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent μ f s) (hg : LaplaceConvergent μ g s) :
    LaplaceConvergent μ (fun t => f t + g t) s :=
  laplaceIntegral.convergent_add (μ := μ) hf hg

/-- Convergence is preserved by scalar multiplication. -/
theorem smul (c : ℂ) {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent μ f s) :
    LaplaceConvergent μ (fun t => c • f t) s :=
  laplaceIntegral.convergent_smul (μ := μ) c hf

/-- Convergence is preserved by negation. -/
theorem neg {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent μ f s) :
    LaplaceConvergent μ (fun t => - f t) s := by
  simpa using (smul (μ := μ) (c := (-1 : ℂ)) (f := f) (s := s) hf)

/-- Convergence is preserved by subtraction. -/
theorem sub {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent μ f s) (hg : LaplaceConvergent μ g s) :
    LaplaceConvergent μ (fun t => f t - g t) s := by
  simpa [sub_eq_add_neg] using add (μ := μ) (f := f) (g := fun t => - g t) (s := s) hf hg.neg

/-- Convergence is preserved by frequency shift. -/
theorem frequency_shift {f : ℝ → E} {s b : ℂ} :
    LaplaceConvergent μ (fun t => Complex.exp (b * (t : ℂ)) • f t) s ↔
      LaplaceConvergent μ f (s - b) := by
  constructor
  · intro hf
    have hfun :
        (fun t : ℝ => laplaceKernel s t • (Complex.exp (b * (t : ℂ)) • f t)) =
          (fun t : ℝ => laplaceKernel (s - b) t • f t) := by
      funext t
      have hb :
          Complex.exp (b * (t : ℂ)) = Complex.exp (-((-b : ℂ) * (t : ℂ))) := by
        simpa using
          congrArg Complex.exp
            (rfl : (b * (t : ℂ)) = -((-b : ℂ) * (t : ℂ)))
      calc
        laplaceKernel s t • (Complex.exp (b * (t : ℂ)) • f t)
            = Complex.exp (b * (t : ℂ)) • (laplaceKernel s t • f t) := by
                rw [smul_comm]
        _ = (Complex.exp (b * (t : ℂ)) * laplaceKernel s t) • f t := by
                rw [mul_smul]
        _ = (Complex.exp (-((-b : ℂ) * (t : ℂ))) * laplaceKernel s t) • f t := by
                rw [hb]
        _ = laplaceKernel (s - b) t • f t := by
                rw [sub_eq_add_neg, laplaceKernel_add]
    simpa [LaplaceConvergent, hfun] using hf
  · intro hf
    have hfun :
        (fun t : ℝ => laplaceKernel (s - b) t • f t) =
          (fun t : ℝ => laplaceKernel s t • (Complex.exp (b * (t : ℂ)) • f t)) := by
      funext t
      have hb :
          Complex.exp (b * (t : ℂ)) = Complex.exp (-((-b : ℂ) * (t : ℂ))) := by
        simpa using
          congrArg Complex.exp
            (rfl : (b * (t : ℂ)) = -((-b : ℂ) * (t : ℂ)))
      calc
        laplaceKernel (s - b) t • f t
            = (Complex.exp (-((-b : ℂ) * (t : ℂ))) * laplaceKernel s t) • f t := by
                rw [sub_eq_add_neg, laplaceKernel_add]
        _ = (Complex.exp (b * (t : ℂ)) * laplaceKernel s t) • f t := by
                rw [hb]
        _ = Complex.exp (b * (t : ℂ)) • (laplaceKernel s t • f t) := by
                rw [mul_smul]
        _ = laplaceKernel s t • (Complex.exp (b * (t : ℂ)) • f t) := by
                rw [smul_comm]
    simpa [LaplaceConvergent, hfun] using hf

end LaplaceConvergent

namespace laplaceIntegralPos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The positive-half-line Laplace transform of the zero function is zero. -/
theorem zero (s : ℂ) :
    laplaceIntegralPos (f := fun _ : ℝ => (0 : E)) s = 0 := by
  simp [laplaceIntegralPos]

/-- Positive-half-line Laplace transform is additive. -/
theorem add {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergentPos f s) (hg : LaplaceConvergentPos g s) :
    laplaceIntegralPos (fun t => f t + g t) s =
      laplaceIntegralPos f s + laplaceIntegralPos g s := by
  change ∫ t in Set.Ioi (0 : ℝ), laplaceKernel s t • (f t + g t) =
    laplaceIntegralPos f s + laplaceIntegralPos g s
  calc
    ∫ t in Set.Ioi (0 : ℝ), laplaceKernel s t • (f t + g t)
        = ∫ t in Set.Ioi (0 : ℝ), laplaceKernel s t • f t +
            laplaceKernel s t • g t := by
            congr with t
            exact smul_add _ _ _
    _ = laplaceIntegralPos f s + laplaceIntegralPos g s := by
          exact MeasureTheory.integral_add hf hg

/-- Positive-half-line Laplace transform is homogeneous. -/
theorem smul (c : ℂ) {f : ℝ → E} {s : ℂ}
    :
    laplaceIntegralPos (fun t => c • f t) s = c • laplaceIntegralPos f s := by
  change ∫ t in Set.Ioi (0 : ℝ), laplaceKernel s t • (c • f t) = c • laplaceIntegralPos f s
  calc
    ∫ t in Set.Ioi (0 : ℝ), laplaceKernel s t • (c • f t)
        = ∫ t in Set.Ioi (0 : ℝ), c • (laplaceKernel s t • f t) := by
            congr with t
            exact smul_comm (laplaceKernel s t) c (f t)
    _ = c • laplaceIntegralPos f s := by
          exact MeasureTheory.integral_smul c (fun t => laplaceKernel s t • f t)

/-- Classical positive-half-line scaling law for the Laplace transform. -/
theorem comp_mul_left {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 < a) :
    laplaceIntegralPos (fun t => f (a * t)) s =
      a⁻¹ • laplaceIntegralPos f (s / (a : ℂ)) := by
  have hmul : (s / (a : ℂ)) * (a : ℂ) = s := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (by exact_mod_cast ha.ne')]
    simp
  have hkernel : ∀ t : ℝ, laplaceKernel (s / (a : ℂ)) (a * t) = laplaceKernel s t := by
    intro t
    have ht : ((a * t : ℝ) : ℂ) = (a : ℂ) * (t : ℂ) := by
      simp
    have harg : (s / (a : ℂ)) * ((a : ℂ) * (t : ℂ)) = s * (t : ℂ) := by
      rw [← mul_assoc, hmul]
    rw [laplaceKernel, laplaceKernel, ht, harg]
  have h := MeasureTheory.integral_comp_mul_left_Ioi
    (g := fun t : ℝ => laplaceKernel (s / (a : ℂ)) t • f t) (a := (0 : ℝ)) (b := a) ha
  simpa [laplaceIntegralPos, hkernel] using h

/-- Classical positive-half-line scaling law for the Laplace transform on the right. -/
theorem comp_mul_right {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 < a) :
    laplaceIntegralPos (fun t => f (t * a)) s =
      a⁻¹ • laplaceIntegralPos f (s / (a : ℂ)) := by
  simpa only [mul_comm] using (comp_mul_left (f := f) (s := s) (a := a) ha)

/-- Spectral shift for the positive-half-line Laplace transform. -/
theorem add_spectral {f : ℝ → E} {s c : ℂ} :
    laplaceIntegralPos f (s + c) =
      laplaceIntegralPos (fun t => Complex.exp (-(c * (t : ℂ))) • f t) s := by
  rw [laplaceIntegralPos, laplaceIntegralPos]
  congr with t
  calc
    laplaceKernel (s + c) t • f t
        = (Complex.exp (-(c * (t : ℂ))) * laplaceKernel s t) • f t := by
            rw [laplaceKernel_add]
    _ = Complex.exp (-(c * (t : ℂ))) • (laplaceKernel s t • f t) := by
          rw [mul_smul]
    _ = laplaceKernel s t • (Complex.exp (-(c * (t : ℂ))) • f t) := by
          rw [smul_comm]

/-- Frequency shift for the positive-half-line Laplace integral. -/
theorem frequency_shift {f : ℝ → E} {s b : ℂ} :
    laplaceIntegralPos (fun t => Complex.exp (b * (t : ℂ)) • f t) s =
      laplaceIntegralPos f (s - b) := by
  rw [laplaceIntegralPos, laplaceIntegralPos]
  congr with t
  have hb :
      Complex.exp (b * (t : ℂ)) = Complex.exp (-((-b : ℂ) * (t : ℂ))) := by
    simpa using
      congrArg Complex.exp
        (rfl : (b * (t : ℂ)) = -((-b : ℂ) * (t : ℂ)))
  calc
    laplaceKernel s t • (Complex.exp (b * (t : ℂ)) • f t)
        = Complex.exp (b * (t : ℂ)) • (laplaceKernel s t • f t) := by
            rw [smul_comm]
    _ = (Complex.exp (b * (t : ℂ)) * laplaceKernel s t) • f t := by
            rw [mul_smul]
    _ = (Complex.exp (-((-b : ℂ) * (t : ℂ))) * laplaceKernel s t) • f t := by
            rw [hb]
    _ = laplaceKernel (s - b) t • f t := by
            rw [sub_eq_add_neg, laplaceKernel_add]

end laplaceIntegralPos

namespace LaplaceConvergentPos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The zero function is Laplace-convergent on the positive half-line. -/
theorem zero (s : ℂ) :
    LaplaceConvergentPos (fun _ : ℝ => (0 : E)) s := by
  change MeasureTheory.Integrable (fun t : ℝ => laplaceKernel s t • (0 : E))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  simpa [laplaceKernel] using
    (MeasureTheory.integrableOn_zero (s := Set.Ioi (0 : ℝ)) (μ := MeasureTheory.volume)
      (E := E))

/-- Positive-half-line convergence is preserved by addition. -/
theorem convergent_add {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergentPos f s) (hg : LaplaceConvergentPos g s) :
    LaplaceConvergentPos (fun t => f t + g t) s := by
  change MeasureTheory.Integrable (fun t : ℝ => laplaceKernel s t • (f t + g t))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  have hfun :
      (fun t : ℝ => laplaceKernel s t • (f t + g t)) =
        (fun t : ℝ => laplaceKernel s t • f t + laplaceKernel s t • g t) := by
    funext t
    exact smul_add _ _ _
  simpa [hfun] using hf.integrable.add hg.integrable

/-- Positive-half-line convergence is preserved by scalar multiplication. -/
theorem convergent_smul (c : ℂ) {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergentPos f s) :
    LaplaceConvergentPos (fun t => c • f t) s := by
  change MeasureTheory.Integrable (fun t : ℝ => laplaceKernel s t • (c • f t))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  have hfun :
      (fun t : ℝ => laplaceKernel s t • (c • f t)) =
        (fun t : ℝ => c • (laplaceKernel s t • f t)) := by
    funext t
    exact smul_comm (laplaceKernel s t) c (f t)
  have h : MeasureTheory.Integrable (fun t : ℝ => c • (laplaceKernel s t • f t))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hf.integrable.smul c
  simpa [hfun] using h

/-- Positive-half-line convergence is preserved by negation. -/
theorem neg {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergentPos f s) :
    LaplaceConvergentPos (fun t => - f t) s := by
  simpa using (convergent_smul (E := E) (c := (-1 : ℂ)) (f := f) (s := s) hf)

/-- Positive-half-line convergence is preserved by subtraction. -/
theorem sub {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergentPos f s) (hg : LaplaceConvergentPos g s) :
    LaplaceConvergentPos (fun t => f t - g t) s := by
  simpa [sub_eq_add_neg] using
    (convergent_add (E := E) (f := f) (g := fun t => - g t) (s := s) hf hg.neg)

/-- Positive-half-line convergence is preserved by positive dilation. -/
theorem comp_mul_left {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 < a) :
    LaplaceConvergentPos (fun t => f (a * t)) s ↔ LaplaceConvergentPos f (s / (a : ℂ)) := by
  have hmul : (s / (a : ℂ)) * (a : ℂ) = s := by
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (by exact_mod_cast ha.ne')]
    simp
  have hkernel : ∀ t : ℝ, laplaceKernel (s / (a : ℂ)) (a * t) = laplaceKernel s t := by
    intro t
    have ht : ((a * t : ℝ) : ℂ) = (a : ℂ) * (t : ℂ) := by
      simp
    have harg : (s / (a : ℂ)) * ((a : ℂ) * (t : ℂ)) = s * (t : ℂ) := by
      rw [← mul_assoc, hmul]
    rw [laplaceKernel, laplaceKernel, ht, harg]
  rw [LaplaceConvergentPos, LaplaceConvergentPos]
  simpa [hkernel] using
    (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => laplaceKernel (s / (a : ℂ)) t • f t) 0 ha)

/-- Positive-half-line convergence is preserved by positive right dilation. -/
theorem comp_mul_right {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 < a) :
    LaplaceConvergentPos (fun t => f (t * a)) s ↔ LaplaceConvergentPos f (s / (a : ℂ)) := by
  simpa only [mul_comm] using (comp_mul_left (f := f) (s := s) (a := a) ha)

/-- Positive-half-line convergence is preserved by frequency shift. -/
theorem frequency_shift {f : ℝ → E} {s b : ℂ} :
    LaplaceConvergentPos (fun t => Complex.exp (b * (t : ℂ)) • f t) s ↔
      LaplaceConvergentPos f (s - b) := by
  constructor
  · intro hf
    have hfun :
        (fun t : ℝ => laplaceKernel s t • (Complex.exp (b * (t : ℂ)) • f t)) =
          (fun t : ℝ => laplaceKernel (s - b) t • f t) := by
      funext t
      have hb :
          Complex.exp (b * (t : ℂ)) = Complex.exp (-((-b : ℂ) * (t : ℂ))) := by
        simpa using
          congrArg Complex.exp
            (rfl : (b * (t : ℂ)) = -((-b : ℂ) * (t : ℂ)))
      calc
        laplaceKernel s t • (Complex.exp (b * (t : ℂ)) • f t)
            = Complex.exp (b * (t : ℂ)) • (laplaceKernel s t • f t) := by
                rw [smul_comm]
        _ = (Complex.exp (b * (t : ℂ)) * laplaceKernel s t) • f t := by
                rw [mul_smul]
        _ = (Complex.exp (-((-b : ℂ) * (t : ℂ))) * laplaceKernel s t) • f t := by
                rw [hb]
        _ = laplaceKernel (s - b) t • f t := by
                rw [sub_eq_add_neg, laplaceKernel_add]
    simpa [LaplaceConvergentPos, hfun] using hf
  · intro hf
    have hfun :
        (fun t : ℝ => laplaceKernel (s - b) t • f t) =
          (fun t : ℝ => laplaceKernel s t • (Complex.exp (b * (t : ℂ)) • f t)) := by
      funext t
      have hb :
          Complex.exp (b * (t : ℂ)) = Complex.exp (-((-b : ℂ) * (t : ℂ))) := by
        simpa using
          congrArg Complex.exp
            (rfl : (b * (t : ℂ)) = -((-b : ℂ) * (t : ℂ)))
      calc
        laplaceKernel (s - b) t • f t
            = (Complex.exp (-((-b : ℂ) * (t : ℂ))) * laplaceKernel s t) • f t := by
                rw [sub_eq_add_neg, laplaceKernel_add]
        _ = (Complex.exp (b * (t : ℂ)) * laplaceKernel s t) • f t := by
                rw [hb]
        _ = Complex.exp (b * (t : ℂ)) • (laplaceKernel s t • f t) := by
                rw [mul_smul]
        _ = laplaceKernel s t • (Complex.exp (b * (t : ℂ)) • f t) := by
                rw [smul_comm]
    simpa [LaplaceConvergentPos, hfun] using hf

end LaplaceConvergentPos

namespace laplaceTransformPos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Zero on the positive-half-line Laplace transform. -/
theorem zero (s : ℂ) :
    laplaceTransformPos (f := fun _ : ℝ => (0 : E)) s = 0 := by
  simpa [laplaceTransformPos] using
    (laplaceIntegralPos.zero (E := E) s)

/-- Positive-half-line scaling law for the Laplace transform. -/
theorem comp_mul_left {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 < a) :
    laplaceTransformPos (fun t => f (a * t)) s =
      a⁻¹ • laplaceTransformPos f (s / (a : ℂ)) := by
  simpa [laplaceTransformPos] using
    (laplaceIntegralPos.comp_mul_left (E := E) (f := f) (s := s) (a := a) ha)

end laplaceTransformPos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function has a Laplace transform if it is convergent and the integral equals a value. -/
def HasLaplace (f : ℝ → E) (s : ℂ) (m : E) : Prop :=
  LaplaceConvergent MeasureTheory.volume f s ∧ laplaceTransform f s = m

/-- The zero function has Laplace transform zero. -/
theorem hasLaplace_zero (s : ℂ) : HasLaplace (fun _ : ℝ => (0 : E)) s 0 := by
  refine ⟨?_, ?_⟩
  · simpa [LaplaceConvergent] using
      (MeasureTheory.integrable_zero (μ := MeasureTheory.volume) (E := E))
  · simpa [laplaceTransform] using
      (laplaceIntegral.zero_integral (μ := MeasureTheory.volume) (E := E) s)

/-- HasLaplace is closed under addition. -/
theorem hasLaplace_add {f g : ℝ → E} {s : ℂ} {m n : E}
    (hf : HasLaplace f s m) (hg : HasLaplace g s n) :
    HasLaplace (fun t => f t + g t) s (m + n) := by
  rcases hf with ⟨hfconv, hfm⟩
  rcases hg with ⟨hgconv, hgn⟩
  refine ⟨LaplaceConvergent.add hfconv hgconv, ?_⟩
  calc
    laplaceTransform (fun t => f t + g t) s =
        laplaceIntegral MeasureTheory.volume (fun t => f t + g t) s := rfl
    _ = laplaceIntegral MeasureTheory.volume f s +
          laplaceIntegral MeasureTheory.volume g s := by
          simpa only [laplaceIntegral, smul_add] using
            (laplaceIntegral.add (μ := MeasureTheory.volume) (f := f) (g := g) (s := s)
              hfconv hgconv)
    _ = m + n := by
          have hsum : laplaceIntegral MeasureTheory.volume f s +
              laplaceIntegral MeasureTheory.volume g s = m + n := by
            change laplaceTransform f s + laplaceTransform g s = m + n
            rw [hfm, hgn]
          simpa [laplaceTransform] using hsum

/-- HasLaplace is closed under scalar multiplication. -/
theorem hasLaplace_smul (c : ℂ) {f : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplace f s m) :
    HasLaplace (fun t => c • f t) s (c • m) := by
  rcases hf with ⟨hfconv, hfm⟩
  refine ⟨LaplaceConvergent.smul c hfconv, ?_⟩
  calc
    laplaceTransform (fun t => c • f t) s =
        laplaceIntegral MeasureTheory.volume (fun t => c • f t) s := rfl
    _ = c • laplaceIntegral MeasureTheory.volume f s := by
          exact (laplaceIntegral.smul (μ := MeasureTheory.volume) (c := c) (f := f) (s := s))
    _ = c • m := by
          have hsmul : c • laplaceIntegral MeasureTheory.volume f s = c • m := by
            change c • laplaceTransform f s = c • m
            rw [hfm]
          simpa [laplaceTransform] using hsmul

/-- `HasLaplace` is closed under negation. -/
theorem hasLaplace_neg {f : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplace f s m) :
    HasLaplace (fun t => - f t) s (-m) := by
  simpa [sub_eq_add_neg] using hasLaplace_smul (c := (-1 : ℂ)) (hf := hf)

/-- `HasLaplace` is closed under subtraction. -/
theorem hasLaplace_sub {f g : ℝ → E} {s : ℂ} {m n : E}
    (hf : HasLaplace f s m) (hg : HasLaplace g s n) :
    HasLaplace (fun t => f t - g t) s (m - n) := by
  simpa [sub_eq_add_neg] using hasLaplace_add (hf := hf) (hg := hasLaplace_neg (hf := hg))

/-- The value of a Laplace transform is unique when it exists. -/
theorem hasLaplace_unique {f : ℝ → E} {s : ℂ} {m n : E}
    (hm : HasLaplace f s m) (hn : HasLaplace f s n) :
    m = n := by
  rcases hm with ⟨_, hm⟩
  rcases hn with ⟨_, hn⟩
  calc
    m = laplaceTransform f s := hm.symm
    _ = n := hn

/-- `HasLaplace` transports under left dilation on the whole line. -/
theorem hasLaplace_comp_mul_left {f : ℝ → E} {s : ℂ} {m : E} {a : ℝ} (ha : a ≠ 0)
    (hf : HasLaplace f (s / (a : ℂ)) m) :
    HasLaplace (fun t => f (a * t)) s (|a⁻¹| • m) := by
  rcases hf with ⟨hfconv, hfm⟩
  have hkernel : ∀ t : ℝ, laplaceKernel (s / (a : ℂ)) (a * t) = laplaceKernel s t := by
    intro t
    have ht : ((a * t : ℝ) : ℂ) = (a : ℂ) * (t : ℂ) := by
      simp
    have harg : (s / (a : ℂ)) * ((a : ℂ) * (t : ℂ)) = s * (t : ℂ) := by
      calc
        (s / (a : ℂ)) * ((a : ℂ) * (t : ℂ))
            = (s * (a : ℂ)⁻¹) * ((a : ℂ) * (t : ℂ)) := by rw [div_eq_mul_inv]
        _ = s * ((a : ℂ)⁻¹ * ((a : ℂ) * (t : ℂ))) := by ring
        _ = s * (((a : ℂ)⁻¹ * (a : ℂ)) * (t : ℂ)) := by rw [mul_assoc]
        _ = s * (t : ℂ) := by
              rw [inv_mul_cancel₀ (by exact_mod_cast ha), one_mul]
    rw [laplaceKernel, laplaceKernel, ht, harg]
  have hconv :
      MeasureTheory.Integrable (fun t : ℝ => laplaceKernel s t • f (a * t))
        MeasureTheory.volume := by
    have hconv' :
        MeasureTheory.Integrable
          (fun t : ℝ => laplaceKernel (s / (a : ℂ)) t • f t) MeasureTheory.volume :=
      hfconv
    have hconv'' :
        MeasureTheory.Integrable
          (fun t : ℝ => laplaceKernel (s / (a : ℂ)) (a * t) • f (a * t))
          MeasureTheory.volume :=
      hconv'.comp_mul_left' ha
    convert hconv'' using 1
    funext t
    rw [hkernel]
  refine ⟨?_, ?_⟩
  · simpa [LaplaceConvergent, laplaceIntegral, laplaceTransform, laplaceKernel] using hconv
  · calc
      laplaceTransform (fun t => f (a * t)) s =
          laplaceIntegral MeasureTheory.volume (fun t => f (a * t)) s := rfl
      _ = ∫ t : ℝ, laplaceKernel s t • f (a * t) ∂MeasureTheory.volume := by rfl
      _ = ∫ t : ℝ, laplaceKernel (s / (a : ℂ)) (a * t) • f (a * t) ∂MeasureTheory.volume := by
            congr with t
            rw [hkernel]
      _ = |a⁻¹| • laplaceTransform f (s / (a : ℂ)) := by
            simpa [laplaceTransform, laplaceIntegral] using
              (MeasureTheory.Measure.integral_comp_mul_left
                (g := fun y : ℝ => laplaceKernel (s / (a : ℂ)) y • f y) a)
      _ = |a⁻¹| • m := by rw [hfm]

/-- `HasLaplace` transports under right dilation on the whole line. -/
theorem hasLaplace_comp_mul_right {f : ℝ → E} {s : ℂ} {m : E} {a : ℝ} (ha : a ≠ 0)
    (hf : HasLaplace f (s / (a : ℂ)) m) :
    HasLaplace (fun t => f (t * a)) s (|a⁻¹| • m) := by
  simpa only [mul_comm] using hasLaplace_comp_mul_left (f := f) (s := s) (m := m) (a := a) ha hf

/-- `HasLaplace` transports under frequency shift. -/
theorem hasLaplace_frequency_shift {f : ℝ → E} {s b : ℂ} {m : E}
    (hf : HasLaplace f (s - b) m) :
    HasLaplace (fun t => Complex.exp (b * (t : ℂ)) • f t) s m := by
  rcases hf with ⟨hfconv, hfm⟩
  refine ⟨(LaplaceConvergent.frequency_shift (μ := MeasureTheory.volume) (f := f) (s := s)
      (b := b)).2 hfconv, ?_⟩
  calc
    laplaceTransform (fun t => Complex.exp (b * (t : ℂ)) • f t) s =
        laplaceIntegral MeasureTheory.volume (fun t => Complex.exp (b * (t : ℂ)) • f t) s := rfl
    _ = laplaceIntegral MeasureTheory.volume f (s - b) := by
          exact
            (laplaceIntegral.frequency_shift (μ := MeasureTheory.volume) (E := E) (f := f)
              (s := s) (b := b))
    _ = m := by
          simpa [laplaceTransform] using hfm

namespace laplaceTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The default Laplace transform is homogeneous under left dilation on the whole line. -/
theorem comp_mul_left {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : a ≠ 0) :
    laplaceTransform (fun t => f (a * t)) s =
      |a⁻¹| • laplaceTransform f (s / (a : ℂ)) := by
  have hkernel : ∀ x : ℝ, laplaceKernel (s / (a : ℂ)) (a * x) = laplaceKernel s x := by
    intro x
    have hx : ((a * x : ℝ) : ℂ) = (a : ℂ) * (x : ℂ) := by
      simp
    have hcancel : (a : ℂ)⁻¹ * ((a : ℂ) * (x : ℂ)) = (x : ℂ) := by
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast ha), one_mul]
    have harg : (s / (a : ℂ)) * ((a : ℂ) * (x : ℂ)) = s * (x : ℂ) := by
      rw [div_eq_mul_inv, mul_assoc, hcancel]
    rw [laplaceKernel, laplaceKernel, hx, harg]
  simpa [laplaceTransform, laplaceIntegral, hkernel] using
    (MeasureTheory.Measure.integral_comp_mul_left
      (g := fun y : ℝ => laplaceKernel (s / (a : ℂ)) y • f y) a)

/-- The default Laplace transform is homogeneous under right dilation on the whole line. -/
theorem comp_mul_right {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : a ≠ 0) :
    laplaceTransform (fun t => f (t * a)) s =
      |a⁻¹| • laplaceTransform f (s / (a : ℂ)) := by
  simpa only [mul_comm] using (comp_mul_left (f := f) (s := s) (a := a) ha)

/-- The default Laplace transform transports under frequency shift. -/
theorem frequency_shift {f : ℝ → E} {s b : ℂ} :
    laplaceTransform (fun t => Complex.exp (b * (t : ℂ)) • f t) s =
      laplaceTransform f (s - b) := by
  simpa [laplaceTransform] using
    (laplaceIntegral.frequency_shift (μ := MeasureTheory.volume) (E := E) (f := f) (s := s)
      (b := b))

/-- Spectral shift for the default Laplace transform. -/
theorem add_spectral {f : ℝ → E} (s c : ℂ) :
    laplaceTransform f (s + c) =
      laplaceIntegral MeasureTheory.volume (fun t => Complex.exp (-(c * (t : ℂ))) • f t) s := by
  simpa [laplaceTransform] using
    (laplaceIntegral.add_spectral (μ := MeasureTheory.volume) (E := E) (f := f) (s := s) (c := c))

/-- The Laplace transform of the zero function is zero. -/
theorem zero (s : ℂ) :
    laplaceTransform (f := fun _ : ℝ => (0 : E)) s = 0 := by
  simpa [laplaceTransform] using
    (laplaceIntegral.zero_integral (μ := MeasureTheory.volume) (E := E) s)

/-- Laplace transform is additive on convergent inputs. -/
theorem add {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent MeasureTheory.volume f s)
    (hg : LaplaceConvergent MeasureTheory.volume g s) :
    laplaceTransform (fun t => f t + g t) s =
      laplaceTransform f s + laplaceTransform g s := by
  simpa [laplaceTransform] using
    (laplaceIntegral.add (μ := MeasureTheory.volume) (f := f) (g := g) (s := s) hf hg)

/-- Laplace transform is homogeneous on convergent inputs. -/
theorem smul (c : ℂ) {f : ℝ → E} {s : ℂ}
    :
    laplaceTransform (fun t => c • f t) s = c • laplaceTransform f s := by
  simpa [laplaceTransform] using
    (laplaceIntegral.smul (μ := MeasureTheory.volume) (c := c) (f := f) (s := s))

end laplaceTransform

namespace laplaceTransformPos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Positive-half-line Laplace transform is additive. -/
theorem add {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergentPos f s) (hg : LaplaceConvergentPos g s) :
    laplaceTransformPos (fun t => f t + g t) s =
      laplaceTransformPos f s + laplaceTransformPos g s := by
  simpa [laplaceTransformPos] using
    (laplaceIntegralPos.add (E := E) (f := f) (g := g) (s := s) hf hg)

/-- Positive-half-line Laplace transform is homogeneous. -/
theorem smul (c : ℂ) {f : ℝ → E} {s : ℂ}
    :
    laplaceTransformPos (fun t => c • f t) s = c • laplaceTransformPos f s := by
  simpa [laplaceTransformPos] using
    (laplaceIntegralPos.smul (E := E) (c := c) (f := f) (s := s))

/-- Positive-half-line Laplace transform is homogeneous on the right argument too. -/
theorem comp_mul_right {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 < a) :
    laplaceTransformPos (fun t => f (t * a)) s =
      a⁻¹ • laplaceTransformPos f (s / (a : ℂ)) := by
  simpa only [mul_comm] using
    (comp_mul_left (f := f) (s := s) (a := a) ha)

/-- Positive-half-line Laplace transform transports under frequency shift. -/
theorem frequency_shift {f : ℝ → E} {s b : ℂ} :
    laplaceTransformPos (fun t => Complex.exp (b * (t : ℂ)) • f t) s =
      laplaceTransformPos f (s - b) := by
  simpa [laplaceTransformPos] using
    (laplaceIntegralPos.frequency_shift (E := E) (f := f) (s := s) (b := b))

/-- Spectral shift for the positive-half-line Laplace transform. -/
theorem add_spectral {f : ℝ → E} {s c : ℂ} :
    laplaceTransformPos f (s + c) =
      laplaceTransformPos (fun t => Complex.exp (-(c * (t : ℂ))) • f t) s := by
  simpa [laplaceTransformPos] using
    (laplaceIntegralPos.add_spectral (E := E) (f := f) (s := s) (c := c))

end laplaceTransformPos

/-- Positive-half-line analogue of `HasMellin`. -/
def HasLaplacePos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) (m : E) : Prop :=
  LaplaceConvergentPos f s ∧ laplaceTransformPos f s = m

namespace HasLaplacePos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The zero function has positive-half-line Laplace transform zero. -/
theorem zero (s : ℂ) : HasLaplacePos (fun _ : ℝ => (0 : E)) s 0 := by
  refine ⟨LaplaceConvergentPos.zero (E := E) s, ?_⟩
  simpa [laplaceTransformPos] using (laplaceIntegralPos.zero (E := E) s)

/-- `HasLaplacePos` is closed under addition. -/
theorem add {f g : ℝ → E} {s : ℂ} {m n : E}
    (hf : HasLaplacePos f s m) (hg : HasLaplacePos g s n) :
    HasLaplacePos (fun t => f t + g t) s (m + n) := by
  rcases hf with ⟨hfconv, hfm⟩
  rcases hg with ⟨hgconv, hgn⟩
  refine ⟨LaplaceConvergentPos.convergent_add hfconv hgconv, ?_⟩
  calc
    laplaceTransformPos (fun t => f t + g t) s =
        laplaceTransformPos f s + laplaceTransformPos g s := by
          exact laplaceTransformPos.add (f := f) (g := g) (s := s) hfconv hgconv
    _ = m + n := by rw [hfm, hgn]

/-- `HasLaplacePos` is closed under scalar multiplication. -/
theorem smul (c : ℂ) {f : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplacePos f s m) :
    HasLaplacePos (fun t => c • f t) s (c • m) := by
  rcases hf with ⟨hfconv, hfm⟩
  refine ⟨LaplaceConvergentPos.convergent_smul c hfconv, ?_⟩
  calc
    laplaceTransformPos (fun t => c • f t) s = c • laplaceTransformPos f s := by
      exact laplaceTransformPos.smul c
    _ = c • m := by rw [hfm]

/-- `HasLaplacePos` is closed under negation. -/
theorem neg {f : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplacePos f s m) :
    HasLaplacePos (fun t => - f t) s (-m) := by
  simpa [sub_eq_add_neg] using smul (E := E) (c := (-1 : ℂ)) (hf := hf)

/-- `HasLaplacePos` is closed under subtraction. -/
theorem sub {f g : ℝ → E} {s : ℂ} {m n : E}
    (hf : HasLaplacePos f s m) (hg : HasLaplacePos g s n) :
    HasLaplacePos (fun t => f t - g t) s (m - n) := by
  simpa [sub_eq_add_neg] using add (E := E) (hf := hf) (hg := neg (E := E) (hf := hg))

/-- The value of a positive-half-line Laplace transform is unique when it exists. -/
theorem unique {f : ℝ → E} {s : ℂ} {m n : E}
    (hm : HasLaplacePos f s m) (hn : HasLaplacePos f s n) :
    m = n := by
  rcases hm with ⟨_, hm⟩
  rcases hn with ⟨_, hn⟩
  calc
    m = laplaceTransformPos f s := hm.symm
    _ = n := hn

/-- `HasLaplacePos` transports under positive dilation. -/
theorem comp_mul_left {f : ℝ → E} {s : ℂ} {m : E} {a : ℝ} (ha : 0 < a)
    (hf : HasLaplacePos f (s / (a : ℂ)) m) :
    HasLaplacePos (fun t => f (a * t)) s (a⁻¹ • m) := by
  rcases hf with ⟨hfconv, hfm⟩
  refine ⟨(LaplaceConvergentPos.comp_mul_left (f := f) (s := s) (a := a) ha).2 hfconv, ?_⟩
  calc
    laplaceTransformPos (fun t => f (a * t)) s =
        a⁻¹ • laplaceTransformPos f (s / (a : ℂ)) := by
          exact laplaceTransformPos.comp_mul_left (f := f) (s := s) (a := a) ha
    _ = a⁻¹ • m := by rw [hfm]

/-- `HasLaplacePos` transports under right dilation. -/
theorem comp_mul_right {f : ℝ → E} {s : ℂ} {m : E} {a : ℝ} (ha : 0 < a)
    (hf : HasLaplacePos f (s / (a : ℂ)) m) :
    HasLaplacePos (fun t => f (t * a)) s (a⁻¹ • m) := by
  simpa only [mul_comm] using comp_mul_left (f := f) (s := s) (m := m) (a := a) ha hf

end HasLaplacePos

end InfoGeometry.Analysis.LaplaceTransform
