import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CyclotomicProjectorReadout

set_option synthInstance.maxHeartbeats 100000

/-!
# Constructed fourth-root Fourier projectors

Unlike the existing general readout interface, this owner derives the
projector laws from the single operator identity `U^4 = 1`. It then supplies
that existing interface. Neither a Hodge star nor a degree grading is assumed.
For `U^2 = -1`, the even-indexed Fourier projectors are zero.
-/

noncomputable section

namespace InfoGeometry.Algebra.FourthRootSpectralProjectors

open InfoGeometry.Canonical.CyclotomicProjector

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [IsScalarTower ℂ ℂ E]

local instance : SMulCommClass ℂ ℂ E where
  smul_comm a b x := by
    rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul, mul_comm]

/-- The four complex characters, in spectral index order. -/
def root4 : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]

@[simp] theorem root4_zero : root4 0 = 1 := rfl
@[simp] theorem root4_one : root4 1 = Complex.I := rfl
@[simp] theorem root4_two : root4 2 = -1 := rfl
@[simp] theorem root4_three : root4 3 = -Complex.I := rfl

theorem root4_eq_pow (k : Fin 4) : root4 k = Complex.I ^ k.val := by
  fin_cases k <;> simp [pow_succ]

@[simp] theorem root4_pow_four (k : Fin 4) : root4 k ^ 4 = 1 := by
  fin_cases k <;> simp [pow_succ]

/-- Fourier polynomial: the coefficient of `U^m` is `root4 k ^ (-m)`.
The displayed polynomial avoids integer powers by using fourth-root identities. -/
def projector (U : Module.End ℂ E) (k : Fin 4) : Module.End ℂ E :=
  (1 / 4 : ℂ) •
    (1 + (root4 k ^ 3) • U + (root4 k ^ 2) • (U ^ 2) +
      (root4 k) • (U ^ 3))

@[simp] theorem projector_apply (U : Module.End ℂ E) (k : Fin 4) (x : E) :
    projector U k x = (1 / 4 : ℂ) •
      (x + root4 k ^ 3 • U x + root4 k ^ 2 • U (U x) +
        root4 k • U (U (U x))) := by
  simp [projector, Module.End.mul_apply, pow_succ]

/-- Completeness follows from the scalar Fourier coefficients even before
one imposes a polynomial equation on `U`. -/
theorem projector_sum (U : Module.End ℂ E) : (∑ k, projector U k) = 1 := by
  ext x
  simp only [Fin.sum_univ_four, LinearMap.add_apply, Module.End.one_apply,
    projector_apply]
  simp [pow_succ]
  module

/-- The first genuine spectral law uses `U^4 = 1`. -/
theorem generator_mul_projector (U : Module.End ℂ E) (hU : U ^ 4 = 1) (k : Fin 4) :
    U * projector U k = root4 k • projector U k := by
  have h4 (x : E) : U (U (U (U x))) = x := by
    have h := congrArg (fun T : Module.End ℂ E => T x) hU
    simpa [pow_succ, Module.End.mul_apply] using h
  ext x
  simp only [Module.End.mul_apply, LinearMap.smul_apply, projector_apply,
    map_smul, map_add, h4]
  have hr4 : root4 k * root4 k ^ 3 = 1 := by
    rw [← pow_succ', root4_pow_four]
  have hr3 : root4 k * root4 k ^ 2 = root4 k ^ 3 := by
    rw [← pow_succ']
  have hr2 : root4 k * root4 k = root4 k ^ 2 := by rw [pow_two]
  have hcomm : root4 k • (1 / 4 : ℂ) • (x + root4 k ^ 3 • U x + root4 k ^ 2 • U (U x) + root4 k • U (U (U x))) =
      (1 / 4 : ℂ) • root4 k • (x + root4 k ^ 3 • U x + root4 k ^ 2 • U (U x) + root4 k • U (U (U x))) := by
    rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [hcomm]
  congr 1
  simp only [smul_add]
  rw [← smul_assoc, ← smul_assoc, ← smul_assoc]
  simp only [smul_eq_mul, hr4, hr3, hr2, one_smul]
  module

/-- Fourier evaluation on a root eigenvector. No ambient diagonalization
or finite-dimensionality assumption is used. -/
theorem projector_on_eigenvector (U : Module.End ℂ E) (k l : Fin 4) (x : E)
    (hx : U x = root4 l • x) :
    projector U k x = if k = l then x else 0 := by
  simp only [projector_apply, hx, map_smul]
  rw [← smul_assoc, ← smul_assoc, ← smul_assoc, ← smul_assoc, ← smul_assoc, ← smul_assoc]
  simp only [smul_eq_mul]
  fin_cases k <;> fin_cases l <;>
    norm_num [root4, pow_succ, Complex.I_sq] <;> module

theorem projector_idempotent (U : Module.End ℂ E) (hU : U ^ 4 = 1) (k : Fin 4) :
    projector U k * projector U k = projector U k := by
  ext x
  have he := congrArg (fun T : Module.End ℂ E => T x)
    (generator_mul_projector U hU k)
  change U (projector U k x) = root4 k • projector U k x at he
  change projector U k (projector U k x) = projector U k x
  simpa only [if_pos rfl] using projector_on_eigenvector U k k (projector U k x) he

theorem projector_orthogonal (U : Module.End ℂ E) (hU : U ^ 4 = 1)
    (k l : Fin 4) (hkl : k ≠ l) : projector U k * projector U l = 0 := by
  ext x
  have he := congrArg (fun T : Module.End ℂ E => T x)
    (generator_mul_projector U hU l)
  change U (projector U l x) = root4 l • projector U l x at he
  change projector U k (projector U l x) = 0
  simpa only [if_neg hkl] using projector_on_eigenvector U k l (projector U l x) he

/-- Supply the repository's existing Fourier interface with derived data. -/
def fourthRootReadout (U : Module.End ℂ E) (hU : U ^ 4 = 1) :
    FourierCyclotomicReadout (K := ℂ) (A := Module.End ℂ E) U 4 where
  ζ := Complex.I
  projector := projector U
  idempotent := projector_idempotent U hU
  orthogonal := projector_orthogonal U hU
  complete := projector_sum U
  eigen k := by
    simpa only [root4_eq_pow, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul] using generator_mul_projector U hU k

/-- Spectral synthesis is reused from the general readout owner. -/
theorem spectral_synthesis (U : Module.End ℂ E) (hU : U ^ 4 = 1) :
    U = ∑ k, root4 k • projector U k := by
  simpa only [fourthRootReadout, root4_eq_pow, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul] using spectral_reconstruction (fourthRootReadout U hU)

/-- An element is fixed by the spectral projector exactly when it has the
corresponding eigenvalue. This permits a zero spectral sector. -/
theorem projector_fixed_iff (U : Module.End ℂ E) (hU : U ^ 4 = 1)
    (k : Fin 4) (x : E) : projector U k x = x ↔ U x = root4 k • x := by
  constructor
  · intro hx
    have he := congrArg (fun T : Module.End ℂ E => T x) (generator_mul_projector U hU k)
    change U (projector U k x) = root4 k • projector U k x at he
    rwa [hx] at he
  · intro hx
    simpa only [if_pos rfl] using projector_on_eigenvector U k k x hx

omit [IsScalarTower ℂ ℂ E] in
theorem fourth_power_of_square_neg_one (U : Module.End ℂ E) (hU : U ^ 2 = -1) :
    U ^ 4 = 1 := by
  calc
    U ^ 4 = (U ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [hU]; simp

/-- A complex structure has no eigenvalue +1 in this four-root resolution. -/
theorem projector_zero_of_square_neg_one (U : Module.End ℂ E) (hU : U ^ 2 = -1) :
    projector U 0 = 0 := by
  have h2 (x : E) : U (U x) = -x := by
    have h := congrArg (fun T : Module.End ℂ E => T x) hU
    simpa [pow_two, Module.End.mul_apply] using h
  ext x
  simp only [projector_apply, h2, map_neg, LinearMap.zero_apply, root4_zero]
  norm_num [pow_succ, Complex.I_sq]

/-- A complex structure has no eigenvalue -1 either. -/
theorem projector_two_of_square_neg_one (U : Module.End ℂ E) (hU : U ^ 2 = -1) :
    projector U 2 = 0 := by
  have h2 (x : E) : U (U x) = -x := by
    have h := congrArg (fun T : Module.End ℂ E => T x) hU
    simpa [pow_two, Module.End.mul_apply] using h
  ext x
  simp only [projector_apply, h2, map_neg, LinearMap.zero_apply, root4_two]
  norm_num [pow_succ, Complex.I_sq]

theorem projector_one_of_square_neg_one (U : Module.End ℂ E) (hU : U ^ 2 = -1) :
    projector U 1 = (1 / 2 : ℂ) • (1 - Complex.I • U) := by
  have h2 (x : E) : U (U x) = -x := by
    have h := congrArg (fun T : Module.End ℂ E => T x) hU
    simpa [pow_two, Module.End.mul_apply] using h
  ext x
  simp only [projector_apply, h2, map_neg, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.one_apply, root4_one]
  norm_num [pow_succ, Complex.I_sq]
  module

theorem projector_three_of_square_neg_one (U : Module.End ℂ E) (hU : U ^ 2 = -1) :
    projector U 3 = (1 / 2 : ℂ) • (1 + Complex.I • U) := by
  have h2 (x : E) : U (U x) = -x := by
    have h := congrArg (fun T : Module.End ℂ E => T x) hU
    simpa [pow_two, Module.End.mul_apply] using h
  ext x
  simp only [projector_apply, h2, map_neg, LinearMap.smul_apply,
    LinearMap.add_apply, Module.End.one_apply, root4_three]
  norm_num [pow_succ, Complex.I_sq]
  module

/-- Only the two imaginary-root sectors can survive for a square-minus-one operator. -/
theorem two_sector_resolution (U : Module.End ℂ E) (hU : U ^ 2 = -1) :
    projector U 1 + projector U 3 = 1 := by
  have hs := projector_sum U
  simpa only [Fin.sum_univ_four, projector_zero_of_square_neg_one U hU,
    projector_two_of_square_neg_one U hU, zero_add, add_zero] using hs

end InfoGeometry.Algebra.FourthRootSpectralProjectors
