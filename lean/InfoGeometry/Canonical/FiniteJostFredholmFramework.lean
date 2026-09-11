import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Geometry.FiniteMatrixResolventKernel

/-!
# Finite self-adjoint Jost/Fredholm framework

This is the finite-dimensional part of the Jost/Fredholm channel.  A
self-adjoint Hamiltonian is an explicit complex matrix satisfying the native
conjugate-transpose equation.  Its Jost matrix is `z • 1 - H`, and the finite
Fredholm divisor is its determinant.

No infinite Fredholm determinant, trace-class limit, or identification with a
zeta function is asserted here.  The resolvent existence statement is tied to
the existing two-sided `MatrixResolventKernel` owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteJostFredholmFramework

open InfoGeometry.Geometry.FiniteMatrixResolventKernel

abbrev FiniteHamiltonian (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix n n ℂ

structure SelfAdjointHamiltonian
    (n : Type*) [Fintype n] [DecidableEq n] where
  operator : FiniteHamiltonian n
  selfAdjoint : operator.conjTranspose = operator

def jostMatrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) (z : ℂ) : Matrix n n ℂ :=
  resolventDiff z H.operator

def finiteFredholmDivisor
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) (z : ℂ) : ℂ :=
  Matrix.det (jostMatrix H z)

/-- Finite relative Fredholm/scattering readout between two Hamiltonians. -/
def finiteRelativeFredholmRatio
    {n : Type*} [Fintype n] [DecidableEq n]
    (H Href : SelfAdjointHamiltonian n) (z : ℂ) : ℂ :=
  finiteFredholmDivisor H z / finiteFredholmDivisor Href z

theorem finiteRelativeFredholmRatio_mul_reference
    {n : Type*} [Fintype n] [DecidableEq n]
    (H Href : SelfAdjointHamiltonian n) (z : ℂ)
    (hRef : finiteFredholmDivisor Href z ≠ 0) :
    finiteRelativeFredholmRatio H Href z *
        finiteFredholmDivisor Href z =
      finiteFredholmDivisor H z := by
  unfold finiteRelativeFredholmRatio
  exact div_mul_cancel₀ _ hRef

@[simp] theorem jostMatrix_eq_resolventDiff
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) (z : ℂ) :
    jostMatrix H z = resolventDiff z H.operator :=
  rfl

theorem finiteFredholmDivisor_eq_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) (z : ℂ) :
    finiteFredholmDivisor H z = Matrix.det (resolventDiff z H.operator) :=
  rfl

theorem jostMatrix_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) (z : ℂ) :
    (jostMatrix H z).conjTranspose = jostMatrix H (starRingEnd ℂ z) := by
  simp [jostMatrix, resolventDiff, H.selfAdjoint]

theorem jostMatrix_isSelfAdjoint_of_real
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) (x : ℝ) :
    (jostMatrix H (x : ℂ)).conjTranspose = jostMatrix H (x : ℂ) := by
  simpa using jostMatrix_conjTranspose H (x : ℂ)

theorem finiteFredholmDivisor_star_reflection
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) (z : ℂ) :
    finiteFredholmDivisor H (starRingEnd ℂ z) =
      starRingEnd ℂ (finiteFredholmDivisor H z) := by
  unfold finiteFredholmDivisor
  change
    Matrix.det (jostMatrix H ((starRingEnd ℂ) z)) =
      star (Matrix.det (jostMatrix H z))
  rw [← Matrix.det_conjTranspose, jostMatrix_conjTranspose]

theorem finiteFredholmDivisor_real_parameter_star
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) (x : ℝ) :
    finiteFredholmDivisor H (x : ℂ) =
      starRingEnd ℂ (finiteFredholmDivisor H (x : ℂ)) := by
  simpa using finiteFredholmDivisor_star_reflection H (x : ℂ)

theorem finiteRelativeFredholmRatio_real_parameter_star
    {n : Type*} [Fintype n] [DecidableEq n]
    (H Href : SelfAdjointHamiltonian n) (x : ℝ) :
    finiteRelativeFredholmRatio H Href (x : ℂ) =
      starRingEnd ℂ (finiteRelativeFredholmRatio H Href (x : ℂ)) := by
  unfold finiteRelativeFredholmRatio
  have hH : finiteFredholmDivisor H (x : ℂ) =
      star (finiteFredholmDivisor H (x : ℂ)) := by
    simpa using finiteFredholmDivisor_star_reflection H (x : ℂ)
  have hHref : finiteFredholmDivisor Href (x : ℂ) =
      star (finiteFredholmDivisor Href (x : ℂ)) := by
    simpa using finiteFredholmDivisor_star_reflection Href (x : ℂ)
  calc
    finiteFredholmDivisor H (x : ℂ) /
        finiteFredholmDivisor Href (x : ℂ) =
      star (finiteFredholmDivisor H (x : ℂ)) /
        star (finiteFredholmDivisor Href (x : ℂ)) := by
          exact congrArg₂ (fun a b : ℂ => a / b) hH hHref
    _ = star (finiteFredholmDivisor H (x : ℂ) /
        finiteFredholmDivisor Href (x : ℂ)) := by
          rw [star_div₀]

theorem finiteFredholmDivisor_ne_zero_iff_resolvent
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) (z : ℂ) :
    finiteFredholmDivisor H z ≠ 0 ↔
      ∃ K : MatrixResolventKernel n,
        K.A = H.operator ∧ K.z = z ∧
          K.kernel * resolventDiff K.z K.A = 1 := by
  constructor
  · intro hdet
    have hdetUnit : IsUnit (Matrix.det (resolventDiff z H.operator)) :=
      isUnit_iff_ne_zero.mpr hdet
    have hUnit : IsUnit (resolventDiff z H.operator) := by
      exact (Matrix.isUnit_iff_isUnit_det (A := resolventDiff z H.operator)).mpr hdetUnit
    rcases hUnit with ⟨U, hU⟩
    let K := matrixResolventKernelOfUnit H.operator z U hU
    exact ⟨K, rfl, rfl, K.kernel_mul_diff⟩
  · rintro ⟨K, hA, hz, hright⟩ hzero
    have hdet_zero : Matrix.det (resolventDiff z H.operator) = 0 := by
      simpa [finiteFredholmDivisor] using hzero
    have hright' : K.kernel * resolventDiff z H.operator = 1 := by
      simpa [hA, hz] using hright
    have hmul :
        Matrix.det (resolventDiff z H.operator) * Matrix.det K.kernel = 1 := by
      calc
        Matrix.det (resolventDiff z H.operator) * Matrix.det K.kernel =
            Matrix.det K.kernel * Matrix.det (resolventDiff z H.operator) := by
              rw [mul_comm]
        _ = Matrix.det (K.kernel * resolventDiff z H.operator) := by
              rw [Matrix.det_mul]
        _ = Matrix.det (1 : Matrix n n ℂ) := by rw [hright']
        _ = 1 := Matrix.det_one
    rw [hdet_zero, zero_mul] at hmul
    exact zero_ne_one hmul

theorem finiteFredholmDivisor_eq_zero_iff_no_resolvent
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) (z : ℂ) :
    finiteFredholmDivisor H z = 0 ↔
      ¬ ∃ K : MatrixResolventKernel n,
        K.A = H.operator ∧ K.z = z ∧
          K.kernel * resolventDiff K.z K.A = 1 := by
  constructor
  · intro hzero hex
    have hne : finiteFredholmDivisor H z ≠ 0 :=
      (finiteFredholmDivisor_ne_zero_iff_resolvent H z).mpr hex
    exact hne hzero
  · intro hno
    by_contra hne
    exact hno ((finiteFredholmDivisor_ne_zero_iff_resolvent H z).mp hne)

theorem selfAdjointHamiltonian_operator_is_selfAdjoint
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : SelfAdjointHamiltonian n) :
    H.operator.conjTranspose = H.operator :=
  H.selfAdjoint

end InfoGeometry.Canonical.FiniteJostFredholmFramework
