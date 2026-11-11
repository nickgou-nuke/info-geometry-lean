/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwistorInternalSymmetry
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Witt Gram matrices of actual constituent packets

The native Witt form and infinity form have different joint readouts.  An
explicit two-parameter family realizes both complex values independently.
The traceless Gram invariant below is a matrix quadratic invariant; no spin
representation or physical normalization is inferred from its name.
-/

noncomputable section
namespace InfoGeometry.Twistor.ConstituentWittGram

open PenroseIncidence PerjesConventions InfinityTwistor
open TwistorKinematicTensor TwistorConstituentKinematics TwistorInternalSymmetry
open scoped BigOperators Matrix

/-- The Gram matrix on the existing finite constituent packet. -/
def gram {ι : Type*} [Fintype ι] (Z : Packet ι) : Matrix ι ι ℂ :=
  fun i j => wittPair (Z i) (Z j)

theorem gram_hermitian {ι : Type*} [Fintype ι] (Z : Packet ι) :
    (gram Z)ᴴ = gram Z := by
  ext i j
  exact wittPair_conj (Z j) (Z i)

private theorem wittPair_sum_left {ι : Type*} [Fintype ι]
    (Z : ι → Twistor4) (W : Twistor4) :
    wittPair (∑ i, Z i) W = ∑ i, wittPair (Z i) W := by
  simp [wittPair, Fin.sum_univ_two, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_apply, Finset.sum_mul, Finset.sum_add_distrib]

private theorem wittPair_sum_right {ι : Type*} [Fintype ι]
    (Z : Twistor4) (W : ι → Twistor4) :
    wittPair Z (∑ i, W i) = ∑ i, wittPair Z (W i) := by
  simp [wittPair, Fin.sum_univ_two, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_apply, Finset.mul_sum, Finset.sum_add_distrib]

private theorem wittPair_smul_left (c : ℂ) (Z W : Twistor4) :
    wittPair (c • Z) W = star c * wittPair Z W := by
  simp [wittPair, Fin.sum_univ_two, smul_eq_mul]
  ring

private theorem wittPair_smul_right (c : ℂ) (Z W : Twistor4) :
    wittPair Z (c • W) = c * wittPair Z W := by
  simp [wittPair, Fin.sum_univ_two, smul_eq_mul]
  ring

/-- Native row-label mixing has the displayed conjugate/transpose order.
Right multiplication on twistor columns instead uses `mix Uᵀ`. -/
theorem gram_mix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (Z : Packet ι) :
    gram (mix U Z) = conjugateEntries U * gram Z * Uᵀ := by
  ext i j
  change wittPair (∑ k, U i k • Z k) (∑ l, U j l • Z l) = _
  rw [wittPair_sum_left]
  simp_rw [wittPair_sum_right, wittPair_smul_left, wittPair_smul_right]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, conjugateEntries,
    gram, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem wittPair_self_im (Z : Twistor4) : (wittPair Z Z).im = 0 := by
  have h : -(wittPair Z Z).im = (wittPair Z Z).im := by
    simpa using congrArg Complex.im (wittPair_conj Z Z)
  linarith

/-- The two on-diagonal entries use the owner's helicity convention. -/
theorem wittPair_self_eq_helicity (Z : Twistor4) :
    wittPair Z Z = ((2 * paperHelicity Z : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re, paperHelicity]
    ring
  · simp [wittPair_self_im]

theorem gram_pair_eq (Z : Packet (Fin 2)) :
    gram Z =
      !![((2 * paperHelicity (Z 0) : ℝ) : ℂ), wittPair (Z 0) (Z 1);
         star (wittPair (Z 0) (Z 1)), ((2 * paperHelicity (Z 1) : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact wittPair_self_eq_helicity (Z 0)
  · rfl
  · exact (wittPair_conj (Z 0) (Z 1)).symm
  · exact wittPair_self_eq_helicity (Z 1)

/-- The Gram determinant is the conformal pairing invariant, with the
factor fixed by `paperHelicity`; it is not the momentum determinant. -/
theorem gram_pair_determinant (Z : Packet (Fin 2)) :
    (gram Z).det =
      ((4 * paperHelicity (Z 0) * paperHelicity (Z 1) -
        Complex.normSq (wittPair (Z 0) (Z 1)) : ℝ) : ℂ) := by
  rw [gram_pair_eq]
  simp [Matrix.det_fin_two, Complex.normSq_eq_conj_mul_self]
  ring

/-- Fixed first constituent for the joint-readout section. -/
def realizationFirst : Twistor4 := (0, ![1, 0])

/-- The lower parameter controls infinity pairing; the upper parameter
controls Witt pairing, on the same native twistor carrier. -/
def realizationSecond (t z : ℂ) : Twistor4 := (![z, 0], ![0, t])

@[simp] theorem realization_infinity (t z : ℂ) :
    infinityTwistor realizationFirst (realizationSecond t z) = t := by
  simp [infinityTwistor, realizationFirst, realizationSecond]

@[simp] theorem realization_witt (t z : ℂ) :
    wittPair realizationFirst (realizationSecond t z) = z := by
  simp [wittPair, realizationFirst, realizationSecond, Fin.sum_univ_two]

@[simp] theorem realization_first_null :
    wittPair realizationFirst realizationFirst = 0 := by
  simp [wittPair, realizationFirst]

@[simp] theorem realization_second_null (t z : ℂ) :
    wittPair (realizationSecond t z) (realizationSecond t z) = 0 := by
  simp [wittPair, realizationSecond, Fin.sum_univ_two]

@[simp] theorem realization_mass (t z : ℂ) :
    pairMassSq realizationFirst (realizationSecond t z) = Complex.normSq t := by
  simp [pairMassSq, spinorMinor, realizationFirst, realizationSecond]

/-- Both complex readouts are jointly surjective, even on self-null columns. -/
theorem joint_readouts_surjective :
    Function.Surjective
      (fun p : Twistor4 × Twistor4 =>
        (infinityTwistor p.1 p.2, wittPair p.1 p.2)) := by
  rintro ⟨t, z⟩
  exact ⟨(realizationFirst, realizationSecond t z),
    Prod.ext (realization_infinity t z) (realization_witt t z)⟩

theorem realization_gram (t z : ℂ) :
    gram ![realizationFirst, realizationSecond t z] = !![0, z; star z, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, wittPair, realizationFirst, realizationSecond, Fin.sum_univ_two]

theorem realization_gram_determinant (t z : ℂ) :
    (gram ![realizationFirst, realizationSecond t z]).det =
      -(Complex.normSq z : ℂ) := by
  rw [realization_gram]
  simp [Matrix.det_fin_two, Complex.normSq_eq_conj_mul_self, mul_comm]

/-- Traceless part of an actual two-by-two matrix. -/
def traceless (H : ComplexSpacetime) : ComplexSpacetime :=
  H - (Matrix.trace H / 2) • (1 : ComplexSpacetime)

/-- The half-trace of the square, before imposing Hermiticity. -/
def tracelessQuadratic (H : ComplexSpacetime) : ℂ :=
  Matrix.trace (traceless H * traceless H) / 2

theorem traceless_gram_eq (Z : Packet (Fin 2)) :
    traceless (gram Z) =
      !![((paperHelicity (Z 0) - paperHelicity (Z 1) : ℝ) : ℂ),
          wittPair (Z 0) (Z 1);
          star (wittPair (Z 0) (Z 1)),
          -((paperHelicity (Z 0) - paperHelicity (Z 1) : ℝ) : ℂ)] := by
  rw [gram_pair_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceless, Matrix.trace, Fin.sum_univ_two, smul_eq_mul] <;>
    push_cast <;> ring

/-- Full matrix square, with a nonnegative real scalar coefficient. -/
theorem traceless_gram_square (Z : Packet (Fin 2)) :
    traceless (gram Z) * traceless (gram Z) =
      (((paperHelicity (Z 0) - paperHelicity (Z 1)) ^ 2 +
          Complex.normSq (wittPair (Z 0) (Z 1)) : ℝ) : ℂ) •
        (1 : ComplexSpacetime) := by
  rw [traceless_gram_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul,
      Complex.normSq_eq_conj_mul_self] <;> push_cast <;> ring

theorem tracelessQuadratic_gram (Z : Packet (Fin 2)) :
    tracelessQuadratic (gram Z) =
      (((paperHelicity (Z 0) - paperHelicity (Z 1)) ^ 2 +
          Complex.normSq (wittPair (Z 0) (Z 1)) : ℝ) : ℂ) := by
  unfold tracelessQuadratic
  rw [traceless_gram_square, Matrix.trace_smul, Matrix.trace_one]
  norm_num [smul_eq_mul]

theorem tracelessQuadratic_gram_nonneg (Z : Packet (Fin 2)) :
    0 ≤ (tracelessQuadratic (gram Z)).re := by
  rw [tracelessQuadratic_gram]
  simp only [Complex.ofReal_re]
  exact add_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)

end InfoGeometry.Twistor.ConstituentWittGram
