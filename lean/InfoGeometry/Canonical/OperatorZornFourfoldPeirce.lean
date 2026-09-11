import InfoGeometry.Canonical.OperatorZornMatrixPeirce
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CyclotomicProjectorReadout

/-!
# Fourfold Fourier resolution in the coefficient algebra

The sixteen full Zorn corners are retained. These finite coefficient sectors
are not identified with physical generations. Their laws are constructed.
-/

noncomputable section
set_option maxHeartbeats 1000000
namespace InfoGeometry.Canonical.OperatorZornFourfoldPeirce

open InfoGeometry.Physics.NCG
open OperatorZornCoefficientNucleus OperatorZornMatrixPeirce CyclotomicProjector
open scoped BigOperators Matrix

abbrev Coeff := Matrix (Fin 4) (Fin 4) ℂ
abbrev projector (k : Fin 4) : Coeff := coefficientProjector k

def clock : Coeff := Matrix.diagonal (fun j => Complex.I ^ j.val)

def raising : Coeff := fun i j => if i.val = j.val + 1 then 1 else 0

def fourierProjector (k : Fin 4) : Coeff :=
  (1/4 : ℂ) • ∑ m : Fin 4, ((-Complex.I) ^ (k.val * m.val)) • clock ^ m.val

theorem projector_product (j k : Fin 4) :
    projector j * projector k = if j = k then projector k else 0 :=
  coefficientProjector_product j k

@[simp] theorem projector_idempotent (k : Fin 4) : projector k * projector k = projector k :=
  coefficientProjector_idempotent k

theorem projector_orthogonal (j k : Fin 4) (h : j ≠ k) : projector j * projector k = 0 :=
  coefficientProjector_orthogonal j k h

theorem projector_complete : (∑ k : Fin 4, projector k) = 1 := coefficientProjector_complete

theorem clock_fourth : clock ^ 4 = (1 : Coeff) := by
  rw [clock, Matrix.diagonal_pow]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.diagonal, Complex.I_sq, pow_succ]

theorem fourierProjector_eq (k : Fin 4) : fourierProjector k = projector k := by
  simp only [fourierProjector, clock, Matrix.diagonal_pow]
  have hdiag : ∀ (k i : Fin 4),
      (1 / 4 : ℂ) * ∑ m : Fin 4, (-Complex.I) ^ (k.val * m.val) *
        (Complex.I ^ i.val) ^ m.val = if i = k then 1 else 0 := by
    intro k i
    fin_cases k <;> fin_cases i <;>
      norm_num [Fin.sum_univ_succ, Complex.I_sq, pow_succ]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    simpa [projector, coefficientProjector, Matrix.diagonal] using hdiag k i
  · simp [projector, coefficientProjector, Matrix.diagonal, hij]

theorem clock_projector (k : Fin 4) :
    clock * projector k = (Complex.I ^ k.val) • projector k := by
  ext a b
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    norm_num [clock, projector, coefficientProjector, Matrix.diagonal, Matrix.mul_apply,
      Fin.sum_univ_succ, Complex.I_sq, pow_succ]

def fourfoldReadout : FourierCyclotomicReadout (K := ℂ) (A := Coeff) clock 4 where
  ζ := Complex.I
  projector := projector
  idempotent := projector_idempotent
  orthogonal := projector_orthogonal
  complete := projector_complete
  eigen k := by
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact clock_projector k

theorem clock_raising_qcommute : clock * raising = Complex.I • (raising * clock) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [clock, raising, Matrix.diagonal, Matrix.mul_apply,
      Fin.sum_univ_succ, Complex.I_sq, pow_succ] <;> simp_all

theorem raising_fourth : raising ^ 4 = (0 : Coeff) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [raising, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem raising_cube_ne_zero : raising ^ 3 ≠ (0 : Coeff) := by
  intro h
  have h30 := congrArg (fun M : Coeff => M 3 0) h
  norm_num [raising, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ] at h30

theorem clock_raising_not_source_commutator :
    clock * raising - raising * clock ≠ Complex.I • raising := by
  intro h
  have h10 := congrArg (fun M : Coeff => (M 1 0).re) h
  norm_num [clock, raising, Matrix.diagonal, Matrix.mul_apply,
    Fin.sum_univ_succ, Complex.I_sq, pow_succ] at h10

theorem raising_projector_shift (k : Fin 4) :
    raising * projector k = projector (k + 1) * raising := by
  ext a b
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    norm_num [raising, projector, coefficientProjector, Matrix.diagonal,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> simp_all

theorem raising_fourierProjector_shift (k : Fin 4) :
    raising * fourierProjector k = fourierProjector (k + 1) * raising := by
  simp only [fourierProjector_eq, raising_projector_shift]

def sector (j k : Fin 4) (X : OperatorZornMatrix Coeff) : OperatorZornMatrix Coeff :=
  corner (projector j) (projector k) X

theorem sixteen_sector_reconstruction (X : OperatorZornMatrix Coeff) :
    (∑ j : Fin 4, ∑ k : Fin 4, sector j k X) = X :=
  corner_reconstruction projector projector_complete X

theorem sector_product_zero (j k l m : Fin 4) (h : k ≠ l)
    (X Y : OperatorZornMatrix Coeff) : sector j k X * sector l m Y = 0 :=
  corner_product_zero _ _ _ _ (projector_orthogonal k l h) X Y

theorem sector_product_matching (j k m : Fin 4) (X Y : OperatorZornMatrix Coeff) :
    sector j k X * sector k m Y =
      sector j m (X * (diagonalCoefficient (projector k) * Y)) := by
  unfold sector
  rw [corner_product, projector_idempotent]

def mixingWitness : OperatorZornMatrix Coeff := diagonalCoefficient raising

theorem mixingWitness_ne_zero : mixingWitness ≠ 0 := by
  intro h
  have hz : raising = 0 := congrArg NCZornElement.n_plus h
  have h10 := congrArg (fun M : Coeff => M 1 0) hz
  norm_num [raising] at h10

theorem diagonal_projector_raising_diagonal (k : Fin 4) :
    projector k * raising * projector k = 0 := by
  ext i j
  rw [mul_coefficientProjector_apply]
  by_cases hj : j = k
  · subst j
    rw [coefficientProjector_mul_apply]
    by_cases hi : i = k
    · subst i
      simp [raising]
    · simp [hi]
  · simp [hj]

theorem diagonal_sectors_lose_mixing :
    (∑ k : Fin 4, sector k k mixingWitness) = 0 := by
  have hzero : ∀ k : Fin 4, sector k k mixingWitness = 0 := by
    intro k
    unfold sector
    simp only [corner_coordinates]
    apply operatorZornMatrix_ext
    · exact diagonal_projector_raising_diagonal k
    · funext i
      have hi := congrArg (fun M : Coeff => M i)
        (diagonal_projector_raising_diagonal k)
      simpa using hi
    · funext i
      simp [mixingWitness, diagonalCoefficient, operatorZornCoordinates]
    · funext i
      simp [mixingWitness, diagonalCoefficient, operatorZornCoordinates]
  simp_rw [hzero]
  simp

end InfoGeometry.Canonical.OperatorZornFourfoldPeirce
