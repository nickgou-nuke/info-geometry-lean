import InfoGeometry.Analysis.BipolarCriticalWindowsVortex
import InfoGeometry.Krein.SplitBoost
import Mathlib
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Two-port scattering and transfer blocks for critical windows

This file separates ordinary unitary scattering from indefinite-metric transfer
matrices.

* `scatteringBlock r t` is the canonical `SU(2)`-form two-port block
  `[[r,-conj t],[t,conj r]]`; normalization is `|r|²+|t|²=1`.
* `hyperbolicTransfer α` is determinant one and preserves the signature matrix
  `J = diag(1,-1)`.

No resonance, bound-state, Josephson, or spectral-zero claim follows merely from
zero transmission. No literal equality `SU(1,1) = SL(2,R)` is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarTwoPortScattering

open InfoGeometry.Analysis.BipolarCriticalWindowsVortex
open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Canonical two-port unitary-form scattering block. -/
def scatteringBlock (r t : ℂ) : M2C :=
  !![r, -(starRingEnd ℂ) t;
     t, (starRingEnd ℂ) r]

/-- Flux normalization for the two amplitudes. -/
def ScatteringNormalized (r t : ℂ) : Prop :=
  Complex.normSq r + Complex.normSq t = 1

/-- Determinant of the scattering block is the total amplitude norm. -/
theorem det_scatteringBlock (r t : ℂ) :
    Matrix.det (scatteringBlock r t) =
      ((Complex.normSq r + Complex.normSq t : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [scatteringBlock]
  rw [Complex.mul_conj, ← Complex.normSq_eq_conj_mul_self]

/-- A normalized scattering block has determinant one. -/
theorem det_scatteringBlock_eq_one {r t : ℂ} (h : ScatteringNormalized r t) :
    Matrix.det (scatteringBlock r t) = 1 := by
  rw [det_scatteringBlock, h]
  norm_num

/-- Exact unitary identity for the canonical scattering block. -/
theorem scatteringBlock_conjTranspose_mul (r t : ℂ) :
    (scatteringBlock r t)ᴴ * scatteringBlock r t =
      ((Complex.normSq r + Complex.normSq t : ℝ) : ℂ) • (1 : M2C) := by
  have hleft (z : ℂ) : (starRingEnd ℂ) z * z = (Complex.normSq z : ℂ) := by
    simpa using Complex.normSq_eq_conj_mul_self.symm
  have hright (z : ℂ) : z * (starRingEnd ℂ) z = (Complex.normSq z : ℂ) := by
    simpa using Complex.mul_conj z
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scatteringBlock, Matrix.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two, hleft, hright] <;> ring

/-- Normalization implies ordinary unitarity. -/
theorem scatteringBlock_unitary {r t : ℂ} (h : ScatteringNormalized r t) :
    (scatteringBlock r t)ᴴ * scatteringBlock r t = 1 := by
  rw [scatteringBlock_conjTranspose_mul, h]
  simp

/-- Reflection amplitude in the left incoming channel. -/
def reflectionAmplitude (r t : ℂ) : ℂ := scatteringBlock r t 0 0

/-- Transmission amplitude from left to right. -/
def transmissionAmplitude (r t : ℂ) : ℂ := scatteringBlock r t 1 0

@[simp] theorem reflectionAmplitude_eq (r t : ℂ) : reflectionAmplitude r t = r := rfl
@[simp] theorem transmissionAmplitude_eq (r t : ℂ) : transmissionAmplitude r t = t := rfl

/-- Vanishing transmission in a normalized two-port block forces unit reflection
probability; no bound-state conclusion is inferred. -/
theorem perfect_reflection_of_zero_transmission
    {r t : ℂ} (h : ScatteringNormalized r t) (ht : t = 0) :
    Complex.normSq r = 1 := by
  rw [ScatteringNormalized, ht] at h
  simpa using h

/-- A scattering datum attached to one critical-line window. -/
structure WindowScattering where
  window : CriticalWindow
  r : ℂ
  t : ℂ
  normalized : ScatteringNormalized r t

namespace WindowScattering

/-- Matrix of the window scattering datum. -/
def matrix (W : WindowScattering) : M2C := scatteringBlock W.r W.t

/-- Every window scattering matrix is unitary. -/
theorem matrix_unitary (W : WindowScattering) : W.matrixᴴ * W.matrix = 1 := by
  exact scatteringBlock_unitary W.normalized

/-- Every window scattering matrix has determinant one. -/
theorem matrix_det (W : WindowScattering) : Matrix.det W.matrix = 1 := by
  exact det_scatteringBlock_eq_one W.normalized

end WindowScattering

/-- Signature matrix for a transfer problem. -/
def JMetric : M2C := !![(1 : ℂ), 0; 0, -1]

/-- Indefinite-metric unitarity predicate. -/
def IsJUnitary (M : M2C) : Prop := Mᴴ * JMetric * M = JMetric

/-- Special `J`-unitary predicate: flux preservation plus determinant one. -/
def IsSpecialJUnitary (M : M2C) : Prop := IsJUnitary M ∧ Matrix.det M = 1

/-- Ordinary unitary scattering preserves the signature form precisely when
the two signature channels do not mix. -/
theorem scatteringBlock_junitary_iff {r t : ℂ} (hn : ScatteringNormalized r t) :
    IsJUnitary (scatteringBlock r t) ↔ t = 0 := by
  have hprod (z : ℂ) : (starRingEnd ℂ) z * z = (Complex.normSq z : ℂ) := by
    simpa using Complex.normSq_eq_conj_mul_self.symm
  constructor
  · intro h
    have he := congrArg (fun M : M2C => M 0 0) h
    have hd : (Complex.normSq r : ℂ) - (Complex.normSq t : ℂ) = 1 := by
      simpa [scatteringBlock, JMetric, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, hprod, sub_eq_add_neg] using he
    have hr := congrArg Complex.re hd
    norm_num at hr
    have ht : Complex.normSq t = 0 := by
      unfold ScatteringNormalized at hn
      linarith
    exact Complex.normSq_eq_zero.mp ht
  · intro ht
    subst t
    have hr := perfect_reflection_of_zero_transmission hn rfl
    unfold IsJUnitary
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [scatteringBlock, JMetric, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, hprod, Complex.mul_conj, hr]

/-- Hyperbolic determinant-one transfer block. -/
def hyperbolicTransfer (α : ℝ) : M2C :=
  !![Complex.cosh (α : ℂ), Complex.sinh (α : ℂ);
     Complex.sinh (α : ℂ), Complex.cosh (α : ℂ)]

@[simp] theorem hyperbolicTransfer_zero : hyperbolicTransfer 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hyperbolicTransfer]

/-- Parameter addition is composition of the transfer action. -/
theorem hyperbolicTransfer_add (α β : ℝ) :
    hyperbolicTransfer (α + β) = hyperbolicTransfer α * hyperbolicTransfer β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicTransfer, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.cosh_add, Complex.sinh_add] <;> ring

/-- Reversing the parameter gives a two-sided inverse. -/
theorem hyperbolicTransfer_inverse (α : ℝ) :
    hyperbolicTransfer α * hyperbolicTransfer (-α) = 1 ∧
      hyperbolicTransfer (-α) * hyperbolicTransfer α = 1 := by
  constructor <;> rw [← hyperbolicTransfer_add] <;> simp

/-- The complex matrix is the coordinate readout of the existing real
split-complex boost action, not a separate dynamical carrier. -/
theorem hyperbolicTransfer_mulVec_splitBoost (α : ℝ)
    (x : InfoGeometry.Krein.SplitBoost.SC) :
    hyperbolicTransfer α *ᵥ ![(x.re : ℂ), (x.hyp : ℂ)] =
      ![((InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.mul
          (InfoGeometry.Krein.SplitBoost.boostElement α) x).re : ℂ),
        ((InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.mul
          (InfoGeometry.Krein.SplitBoost.boostElement α) x).hyp : ℂ)] := by
  ext i
  fin_cases i <;>
    simp [hyperbolicTransfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      InfoGeometry.Krein.SplitBoost.boostElement,
      InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.mul,
      Complex.ofReal_cosh, Complex.ofReal_sinh]; ring

/-- The hyperbolic transfer block has determinant one. -/
theorem hyperbolicTransfer_det (α : ℝ) : Matrix.det (hyperbolicTransfer α) = 1 := by
  rw [Matrix.det_fin_two]
  simpa [hyperbolicTransfer, pow_two, sub_eq_add_neg] using
    (Complex.cosh_sq_sub_sinh_sq (α : ℂ))

/-- The hyperbolic transfer block preserves the signature form. -/
theorem hyperbolicTransfer_junitary (α : ℝ) : IsJUnitary (hyperbolicTransfer α) := by
  unfold IsJUnitary
  have hcosh : (starRingEnd ℂ) (Complex.cosh (α : ℂ)) = Complex.cosh (α : ℂ) := by
    simpa using (Complex.cosh_conj (α : ℂ)).symm
  have hsinh : (starRingEnd ℂ) (Complex.sinh (α : ℂ)) = Complex.sinh (α : ℂ) := by
    simpa using (Complex.sinh_conj (α : ℂ)).symm
  have hident : Complex.cosh (α : ℂ) ^ 2 - Complex.sinh (α : ℂ) ^ 2 = 1 :=
    Complex.cosh_sq_sub_sinh_sq (α : ℂ)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [hyperbolicTransfer, JMetric, Matrix.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two, hcosh, hsinh]
    convert hident using 1; ring
  · simp [hyperbolicTransfer, JMetric, Matrix.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two, hcosh, hsinh]
    ring
  · simp [hyperbolicTransfer, JMetric, Matrix.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two, hcosh, hsinh]
    ring
  · simp [hyperbolicTransfer, JMetric, Matrix.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two, hcosh, hsinh]
    convert congrArg Neg.neg hident using 1; ring

/-- Positive-definite unitarity holds only at the identity parameter. -/
theorem hyperbolicTransfer_unitary_iff (α : ℝ) :
    (hyperbolicTransfer α)ᴴ * hyperbolicTransfer α = 1 ↔ α = 0 := by
  constructor
  · intro h
    have he := congrArg (fun M : M2C => (M 0 0).re) h
    have hs : Real.cosh α ^ 2 + Real.sinh α ^ 2 = 1 := by
      simpa [hyperbolicTransfer, Matrix.conjTranspose, Matrix.mul_apply,
        Fin.sum_univ_two, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
        pow_two] using he
    have hi := Real.cosh_sq_sub_sinh_sq α
    have hz : Real.sinh α = 0 := by nlinarith [sq_nonneg (Real.sinh α)]
    exact Real.sinh_eq_zero.mp hz
  · rintro rfl
    simp

/-- Therefore the hyperbolic block is special `J`-unitary. -/
theorem hyperbolicTransfer_special (α : ℝ) :
    IsSpecialJUnitary (hyperbolicTransfer α) :=
  ⟨hyperbolicTransfer_junitary α, hyperbolicTransfer_det α⟩

/-- Compact scattering/transfer separation packet. -/
theorem scattering_transfer_packet
    {r t : ℂ} (h : ScatteringNormalized r t) (α : ℝ) :
    (scatteringBlock r t)ᴴ * scatteringBlock r t = 1 ∧
      Matrix.det (scatteringBlock r t) = 1 ∧
      IsSpecialJUnitary (hyperbolicTransfer α) := by
  exact ⟨scatteringBlock_unitary h,
    det_scatteringBlock_eq_one h,
    hyperbolicTransfer_special α⟩

end InfoGeometry.Canonical.BipolarTwoPortScattering
