import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Complex data as paired real planes

This is the finite constructive core of Sangston's "Geometry of Complex Data":
a complex data vector is represented as one real two-plane per sample.  The
module proves the norm and Hermitian-inner-product readout identities without
introducing detector optimality or stochastic assumptions.
-/

noncomputable section

namespace InfoGeometry.Signal.ComplexRealification

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Finite complex data indexed by `ι`. -/
abbrev ComplexData (ι : Type*) := ι → ℂ

/-- Real paired-plane data: in-phase and quadrature coordinates at each index. -/
abbrev RealPlaneData (ι : Type*) := ι → ℝ × ℝ

/-- Realification of a finite complex vector as paired real coordinates. -/
def realify (z : ComplexData ι) : RealPlaneData ι :=
  fun i => ((z i).re, (z i).im)

/-- Squared norm of paired real data. -/
def realNormSq (x : RealPlaneData ι) : ℝ :=
  ∑ i, ((x i).1 ^ 2 + (x i).2 ^ 2)

/-- Squared norm of finite complex data. -/
def complexNormSq (z : ComplexData ι) : ℝ :=
  ∑ i, Complex.normSq (z i)

/-- Euclidean dot product of paired real data. -/
def realDot (x y : RealPlaneData ι) : ℝ :=
  ∑ i, ((x i).1 * (y i).1 + (x i).2 * (y i).2)

/--
Quadrature dot product corresponding to the imaginary part of
`∑ i, conj (s i) * z i`.
-/
def quadratureDot (s z : RealPlaneData ι) : ℝ :=
  ∑ i, ((s i).1 * (z i).2 - (s i).2 * (z i).1)

/-- Finite Hermitian inner product, linear in the second argument. -/
def hermitianInner (s z : ComplexData ι) : ℂ :=
  ∑ i, star (s i) * z i

/-- Realification preserves squared norm. -/
theorem realification_normSq_eq_complexNormSq (z : ComplexData ι) :
    realNormSq (realify z) = complexNormSq z := by
  unfold realNormSq realify complexNormSq
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Complex.normSq_apply]
  ring

/-- The real part of the Hermitian inner product is the paired real dot product. -/
theorem hermitian_re_eq_realDot (s z : ComplexData ι) :
    realDot (realify s) (realify z) = (hermitianInner s z).re := by
  unfold realDot realify hermitianInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

/-- The imaginary part of the Hermitian inner product is the quadrature dot product. -/
theorem hermitian_im_eq_quadratureDot (s z : ComplexData ι) :
    quadratureDot (realify s) (realify z) = (hermitianInner s z).im := by
  unfold quadratureDot realify hermitianInner
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Hermitian squared magnitude equals the sum of squared real and quadrature readouts. -/
theorem hermitian_normSq_eq_realDot_sq_add_quadratureDot_sq (s z : ComplexData ι) :
    Complex.normSq (hermitianInner s z) =
      realDot (realify s) (realify z) ^ 2 + quadratureDot (realify s) (realify z) ^ 2 := by
  rw [Complex.normSq_apply]
  rw [← hermitian_re_eq_realDot (s := s) (z := z)]
  rw [← hermitian_im_eq_quadratureDot (s := s) (z := z)]
  ring

end InfoGeometry.Signal.ComplexRealification
