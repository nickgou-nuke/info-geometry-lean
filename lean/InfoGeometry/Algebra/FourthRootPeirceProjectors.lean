import Mathlib
import InfoGeometry.Core.FinitePeirceMatrix
import InfoGeometry.Canonical.CyclotomicProjectorReadout

/-!
# Constructed fourth-order Fourier projectors in any complex associative algebra

The projector laws are derived from `U^4 = 1`. Only afterwards are the native
complete-idempotent predicate and the repository's Fourier readout populated.
The `U^2 = -1` case has exactly the two possibly nonzero ±i projections;
it is not a four-degree exterior decomposition.
-/

noncomputable section

namespace InfoGeometry.Algebra.FourthRootPeirceProjectors

open scoped BigOperators
open InfoGeometry.Core.FinitePeirceMatrix
open InfoGeometry.Canonical.CyclotomicProjector

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The four scalar characters in the canonical order. -/
def phase (k : Fin 4) : ℂ := Complex.I ^ k.val

/-- The finite Fourier polynomial, using zeta^(-1)=zeta^3 for fourth roots. -/
def projector (U : A) (k : Fin 4) : A :=
  (1 / 4 : ℂ) • (1 + (phase k)^3 • U + (phase k)^2 • U^2 + phase k • U^3)

@[simp] theorem phase_fourth (k : Fin 4) : phase k ^ 4 = 1 := by
  fin_cases k <;> norm_num [phase, pow_succ, Complex.I_mul_I]

lemma I_mul_I_mul (c : ℂ) : Complex.I * (c * Complex.I) = -c := by
  calc Complex.I * (c * Complex.I) = (Complex.I * Complex.I) * c := by ring
  _ = -1 * c := by rw [Complex.I_mul_I]
  _ = -c := by ring

lemma mul_I_mul_I (c : ℂ) : (c * Complex.I) * Complex.I = -c := by
  calc (c * Complex.I) * Complex.I = c * (Complex.I * Complex.I) := by ring
  _ = c * -1 := by rw [Complex.I_mul_I]
  _ = -c := by ring

lemma I_pow_three : Complex.I ^ 3 = -Complex.I := by
  calc Complex.I ^ 3 = (Complex.I * Complex.I) * Complex.I := by ring
  _ = -1 * Complex.I := by rw [Complex.I_mul_I]
  _ = -Complex.I := by ring

lemma I_sq : Complex.I ^ 2 = -1 := Complex.I_sq

/-- The scalar coefficients agree with the attachment's inverse-character formula. -/
theorem projector_fourier_sum (U : A) (k : Fin 4) :
    projector U k = (1/4 : ℂ) •
      ∑ m : Fin 4, ((phase k) ^ m.val)⁻¹ • U ^ m.val := by
  fin_cases k <;>
    norm_num [projector, phase, Fin.sum_univ_succ, pow_succ,
      Complex.I_mul_I, Complex.inv_I] <;> module

/-- Cyclic closure is used to derive the eigenvalue equation, not assume it. -/
theorem projector_eigen (U : A) (hU : U^4 = 1) (k : Fin 4) :
    U * projector U k = phase k • projector U k := by
  have h2 : U * U = U^2 := (pow_two U).symm
  have h3 : U * U^2 = U^3 := (pow_succ' U 2).symm
  have h4 : U * U^3 = 1 := by
    calc
      U * U^3 = U^4 := (pow_succ' U 3).symm
      _ = 1 := hU
  simp only [projector, mul_smul_comm, mul_add, mul_one, h2, h3, h4,
    smul_add (M := ℂ), smul_smul (M := ℂ)]
  fin_cases k <;> (
    norm_num [phase, pow_succ, Complex.I_mul_I]
    try simp only [I_mul_I_mul]
    norm_num
    module
  )

/-- Powers act on an eigenvector with the corresponding scalar powers. -/
theorem power_on_eigenvector (U x : A) (z : ℂ) (hx : U*x = z • x) (m : ℕ) :
    U^m * x = z^m • x := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, hx, smul_smul (M := ℂ), pow_succ]

/-- Finite Fourier orthogonality, evaluated on a genuine operator eigenvector. -/
theorem projector_on_eigenvector (U x : A) (j k : Fin 4)
    (hx : U*x = phase k • x) :
    projector U j * x = if j = k then x else 0 := by
  simp only [projector, smul_mul_assoc, add_mul, one_mul,
    power_on_eigenvector U x (phase k) hx, hx, smul_add (M := ℂ), smul_smul (M := ℂ)]
  fin_cases j <;> fin_cases k <;> (
    norm_num [phase, pow_succ, Complex.I_mul_I]
    try simp only [mul_I_mul_I]
    try norm_num
    try module
  )

attribute [local instance] smulCommClass_self

instance instAlgEnd {E : Type*} [AddCommGroup E] [Module ℂ E] : Algebra ℂ (Module.End ℂ E) :=
  @Module.End.instAlgebra ℂ ℂ E _ _ _ _ _ (smulCommClass_self ℂ E) _ (IsScalarTower.left ℂ)

/-- Powers acting on module eigenvectors, without finite-dimensionality assumptions. -/
theorem power_apply_on_eigenvector {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : Module.End ℂ E) (x : E) (z : ℂ) (hx : T x = z • x) (m : ℕ) :
    (T^m) x = z^m • x := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul (M := ℂ) (α := E), pow_succ]

/-- The projectors select actual module eigenvectors, not just algebra elements. -/
theorem projector_apply_on_eigenvector {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : Module.End ℂ E) (x : E) (j k : Fin 4) (hx : T x = phase k • x) :
    projector T j x = if j = k then x else 0 := by
  simp only [projector, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, power_apply_on_eigenvector T x (phase k) hx,
    hx, smul_add (M := ℂ) (A := E), smul_smul (M := ℂ) (α := E)]
  fin_cases j <;> fin_cases k <;> (
    norm_num [phase, pow_succ, Complex.I_mul_I]
    try simp only [I_mul_I_mul, mul_I_mul_I]
    try norm_num
    try module
  )

/-- All sixteen multiplication laws follow from the proved eigenvector calculation. -/
theorem projector_mul (U : A) (hU : U^4 = 1) (j k : Fin 4) :
    projector U j * projector U k = if j = k then projector U k else 0 :=
  projector_on_eigenvector U (projector U k) j k (projector_eigen U hU k)

/-- Completeness is a polynomial identity, even before imposing U^4=1. -/
theorem projector_sum (U : A) : ∑ k : Fin 4, projector U k = 1 := by
  norm_num [projector, phase, Fin.sum_univ_succ, pow_succ,
    Complex.I_mul_I]; module

/-- A derived native complete orthogonal idempotent family. -/
def completeProjectors (U : A) (hU : U^4 = 1) :
    CompleteOrthogonalIdempotents (projector U) where
  idem k := by simpa [IsIdempotentElem] using projector_mul U hU k k
  ortho j k hjk := by simpa only [hjk, ite_false] using projector_mul U hU j k
  complete := projector_sum U

/-- Populate the pre-existing Fourier interface only with proved laws. -/
def fourthRootReadout (U : A) (hU : U^4 = 1) :
    FourierCyclotomicReadout (K := ℂ) (A := A) U 4 where
  ζ := Complex.I
  projector := projector U
  idempotent k := (completeProjectors U hU).idem k |>.eq
  orthogonal j k hjk := (completeProjectors U hU).ortho hjk
  complete := projector_sum U
  eigen k := by
    simpa only [phase, Algebra.smul_def] using projector_eigen U hU k

/-- Spectral synthesis reuses the repository's general readout theorem. -/
theorem projector_synthesis (U : A) (hU : U^4 = 1) :
    U = ∑ k : Fin 4, phase k • projector U k := by
  simpa only [fourthRootReadout, phase, Algebra.smul_def] using
    spectral_reconstruction (fourthRootReadout U hU)

/-- The spectral projectors provide a fully reconstructed constrained Peirce array. -/
def spectralCornerEquiv (U : A) (hU : U^4 = 1) :
    A ≃ₗ[ℂ] cornerSpace (K := ℂ) (projector U) :=
  cornerEquiv (projector U) (completeProjectors U hU)

/-- Composition of all sixteen corners is native matrix multiplication. -/
theorem spectral_blocks_mul (U : A) (hU : U^4 = 1) (x y : A) :
    blocks (projector U) (x*y) = blocks (projector U) x * blocks (projector U) y :=
  blocks_mul (projector U) (completeProjectors U hU) x y

/-- Square-minus-one collapses the formal four-character resolution to two sectors. -/
theorem square_neg_one_projectors (U : A) (hU : U*U = -1) :
    projector U 0 = 0 ∧
    projector U 1 = (1/2 : ℂ) • (1 - Complex.I • U) ∧
    projector U 2 = 0 ∧
    projector U 3 = (1/2 : ℂ) • (1 + Complex.I • U) := by
  have h2 : U^2 = -1 := by simpa only [pow_two] using hU
  have h3 : U^3 = -U := by rw [pow_succ, h2, neg_one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (
    simp only [projector, phase, h2, h3, Fin.isValue]
    norm_num [pow_succ, Complex.I_mul_I, I_pow_three, I_sq]
    try simp only [I_pow_three, I_sq]
    try module
  )

/-- Cyclic sector shifting does not by itself imply nilpotency. -/
def cyclicShift : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,1; 1,0,0,0; 0,1,0,0; 0,0,1,0]

def degreeClock : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal phase

theorem cyclicShift_fourth : cyclicShift^4 = 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cyclicShift, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem degreeClock_fourth : degreeClock^4 = 1 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [degreeClock, phase, Matrix.diagonal, pow_succ,
      Matrix.mul_apply, Fin.sum_univ_succ, Complex.I_mul_I]

/-- The clock-shift covariance holds although the shift has fourth power one. -/
theorem degreeClock_shift : degreeClock * cyclicShift =
    Complex.I • (cyclicShift * degreeClock) := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [degreeClock, cyclicShift, phase, Matrix.diagonal,
      Fin.sum_univ_succ, pow_succ, Complex.I_mul_I]

/-- This shift satisfies the stated sector-ladder relation and is still invertible. -/
theorem cyclicShift_projector (k : Fin 4) :
    cyclicShift * projector degreeClock k =
      projector degreeClock (k + 1) * cyclicShift := by
  fin_cases k
  · change cyclicShift * projector degreeClock 0 = projector degreeClock 1 * cyclicShift
    ext i j
    simp only [projector, degreeClock, Matrix.diagonal_pow,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [cyclicShift, phase, pow_succ, Complex.I_mul_I]
  · change cyclicShift * projector degreeClock 1 = projector degreeClock 2 * cyclicShift
    ext i j
    simp only [projector, degreeClock, Matrix.diagonal_pow,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [cyclicShift, phase, pow_succ, Complex.I_mul_I]
  · change cyclicShift * projector degreeClock 2 = projector degreeClock 3 * cyclicShift
    ext i j
    simp only [projector, degreeClock, Matrix.diagonal_pow,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [cyclicShift, phase, pow_succ, Complex.I_mul_I]
  · change cyclicShift * projector degreeClock 3 = projector degreeClock 0 * cyclicShift
    ext i j
    simp only [projector, degreeClock, Matrix.diagonal_pow,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [cyclicShift, phase, pow_succ, Complex.I_mul_I]

theorem cyclicShift_fourth_ne_zero : cyclicShift^4 ≠ 0 := by
  rw [cyclicShift_fourth]
  exact one_ne_zero

end InfoGeometry.Algebra.FourthRootPeirceProjectors
