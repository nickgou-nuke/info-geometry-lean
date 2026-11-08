import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic elliptic and hyperbolic transform kernels

This file records the finite algebraic kernel behind two transform regimes.
An involution `H` with `H * H = 1` has complementary Peirce projectors;
the corresponding finite hyperbolic kernel is the reciprocal exponential
pair `exp(t)` and `exp(-t)` on those projectors.

This is not an integral Fourier transform, a Haar-measure construction, a
principal-series representation, or an analytic Mellin transform.  It is a
coefficient-algebra identity, intended to be consumed by those later owners.
The carrier is associative (`Ring A`); no assertion is made for the native
nonassociative split-octonion product.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitCliffordTransformKernel

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The `+1` Peirce projector associated with an involution. -/
def peircePlus (H : A) : A := (1 / 2 : ℝ) • (1 + H)

/-- The `-1` Peirce projector associated with an involution. -/
def peirceMinus (H : A) : A := (1 / 2 : ℝ) • (1 - H)

theorem peircePlus_sq (H : A) (hH : H * H = 1) :
    peircePlus H * peircePlus H = peircePlus H := by
  simp [peircePlus, smul_mul_assoc, mul_smul_comm, smul_smul, hH,
    smul_add, add_mul, mul_add]
  module

theorem peirceMinus_sq (H : A) (hH : H * H = 1) :
    peirceMinus H * peirceMinus H = peirceMinus H := by
  simp [peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul, hH,
    smul_sub, sub_mul, mul_sub]
  module

theorem peircePlus_mul_minus (H : A) (hH : H * H = 1) :
    peircePlus H * peirceMinus H = 0 := by
  simp [peircePlus, peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul,
    hH, smul_sub, smul_add, add_mul, mul_add, sub_mul, mul_sub]
  module

theorem peirceMinus_mul_plus (H : A) (hH : H * H = 1) :
    peirceMinus H * peircePlus H = 0 := by
  simp [peircePlus, peirceMinus, smul_mul_assoc, mul_smul_comm, smul_smul,
    hH, smul_sub, smul_add, add_mul, mul_add, sub_mul, mul_sub]

theorem peircePlus_add_minus (H : A) :
    peircePlus H + peirceMinus H = 1 := by
  simp [peircePlus, peirceMinus, smul_add, smul_sub]
  module

theorem peircePlus_sub_minus (H : A) :
    peircePlus H - peirceMinus H = H := by
  simp [peircePlus, peirceMinus, smul_add, smul_sub]
  module

/-- The finite hyperbolic transform kernel associated with `H`. -/
def hyperbolicKernel (H : A) (t : ℝ) : A :=
  Real.exp t • peircePlus H + Real.exp (-t) • peirceMinus H

theorem hyperbolicKernel_zero (H : A) :
    hyperbolicKernel H 0 = 1 := by
  simp [hyperbolicKernel, peircePlus_add_minus]

theorem hyperbolicKernel_mul_peircePlus (H : A) (hH : H * H = 1) (t : ℝ) :
    hyperbolicKernel H t * peircePlus H = Real.exp t • peircePlus H := by
  rw [hyperbolicKernel, add_mul, smul_mul_assoc, smul_mul_assoc]
  rw [peircePlus_sq H hH, peirceMinus_mul_plus H hH]
  simp

theorem hyperbolicKernel_mul_peirceMinus (H : A) (hH : H * H = 1) (t : ℝ) :
    hyperbolicKernel H t * peirceMinus H = Real.exp (-t) • peirceMinus H := by
  rw [hyperbolicKernel, add_mul, smul_mul_assoc, smul_mul_assoc]
  rw [peircePlus_mul_minus H hH, peirceMinus_sq H hH]
  simp

theorem hyperbolicKernel_add (H : A) (hH : H * H = 1) (s t : ℝ) :
    hyperbolicKernel H (s + t) =
      hyperbolicKernel H s * hyperbolicKernel H t := by
  simp only [hyperbolicKernel, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    peircePlus_sq H hH, peircePlus_mul_minus H hH,
    peirceMinus_mul_plus H hH, peirceMinus_sq H hH, smul_smul,
    Real.exp_add]
  have h : -(s + t) = -t + -s := by ring
  rw [h, Real.exp_add]
  module

theorem hyperbolicKernel_mul_neg (H : A) (hH : H * H = 1) (t : ℝ) :
    hyperbolicKernel H t * hyperbolicKernel H (-t) = 1 := by
  rw [← hyperbolicKernel_add H hH t (-t), add_neg_cancel,
    hyperbolicKernel_zero]

/-- The finite elliptic kernel associated with a square root of `-1`. -/
def ellipticKernel (J : A) (t : ℝ) : A :=
  Real.cos t • 1 + Real.sin t • J

theorem ellipticKernel_zero (J : A) :
    ellipticKernel J 0 = 1 := by
  simp [ellipticKernel]

theorem ellipticKernel_add (J : A) (hJ : J * J = -1) (s t : ℝ) :
    ellipticKernel J (s + t) =
      ellipticKernel J s * ellipticKernel J t := by
  simp [ellipticKernel, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, hJ, Real.cos_add, Real.sin_add] <;> module

theorem ellipticKernel_mul_neg (J : A) (hJ : J * J = -1) (t : ℝ) :
    ellipticKernel J t * ellipticKernel J (-t) = 1 := by
  rw [← ellipticKernel_add J hJ t (-t), add_neg_cancel,
    ellipticKernel_zero]

/-! The square-zero/parabolic counterpart. -/

def parabolicKernel (N : A) (t : ℝ) : A := 1 + t • N

theorem parabolicKernel_zero (N : A) :
    parabolicKernel N 0 = 1 := by
  simp [parabolicKernel]

theorem parabolicKernel_add (N : A) (hN : N * N = 0) (s t : ℝ) :
    parabolicKernel N (s + t) =
      parabolicKernel N s * parabolicKernel N t := by
  simp only [parabolicKernel, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, hN, smul_zero, add_zero]
  module

theorem parabolicKernel_mul_neg (N : A) (hN : N * N = 0) (t : ℝ) :
    parabolicKernel N t * parabolicKernel N (-t) = 1 := by
  rw [← parabolicKernel_add N hN t (-t), add_neg_cancel,
    parabolicKernel_zero]

end InfoGeometry.Clifford.SplitCliffordTransformKernel
