import InfoGeometry.Canonical.OperatorZornMatrixPeirce
import InfoGeometry.Canonical.CyclotomicProjectorReadout

/-!
# Fourfold Fourier resolution in the coefficient algebra

The sixteen full Zorn corners are retained. These finite coefficient sectors
are not identified with physical generations. Their laws are constructed.
-/

noncomputable section
namespace InfoGeometry.Canonical.OperatorZornFourfoldPeirce

open InfoGeometry.Physics.NCG
open OperatorZornCoefficientNucleus OperatorZornMatrixPeirce CyclotomicProjector
open scoped BigOperators Matrix

abbrev Coeff := Matrix (Fin 4) (Fin 4) ℂ
abbrev projector (k : Fin 4) : Coeff := coefficientProjector k

def clock : Coeff := Matrix.diagonal (fun j => Complex.I ^ j.val)

/-- The last sector is killed, not wrapped. -/
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

theorem projector_complete : (∑ k : Fin 4, projector k) = 1 :=
  coefficientProjector_complete

theorem clock_fourth : clock ^ 4 = (1 : Coeff) := by
  rw [clock, Matrix.diagonal_pow]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.diagonal, Complex.I_sq, pow_succ]

theorem fourierProjector_eq (k : Fin 4) : fourierProjector k = projector k := by
  simp only [fourierProjector, clock, Matrix.diagonal_pow]
  ext a b
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    norm_num [projector, coefficientProjector, Matrix.diagonal, Fin.sum_univ_succ,
      Complex.I_sq, pow_succ] <;> ring_nf <;> norm_num [Complex.I_sq]

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
      Fin.sum_univ_succ, Complex.I_sq, pow_succ]

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
      Matrix.mul_apply, Fin.sum_univ_succ]

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

theorem diagonal_sectors_lose_mixing :
    (∑ k : Fin 4, sector k k mixingWitness) = 0 := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals simp only [Fin.sum_univ_succ, sector, corner_coordinates]
  all_goals ext a b
  all_goals fin_cases a <;> fin_cases b <;>
    norm_num [mixingWitness, diagonalCoefficient, operatorZornCoordinates,
      projector, coefficientProjector, raising, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_succ]

end InfoGeometry.Canonical.OperatorZornFourfoldPeirce
