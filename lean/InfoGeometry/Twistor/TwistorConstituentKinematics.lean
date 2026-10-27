import InfoGeometry.Twistor.TwistorKinematicTensor

/-!
# Constituent columns, total kinematic tensor, and positive momentum

Columns are the existing four-complex-dimensional twistor coordinates. The
conjugate infinity operation acts on those actual columns, and the total
symmetric tensor agrees with the sum of the single-particle tensors.
-/
noncomputable section
namespace InfoGeometry.Twistor.TwistorConstituentKinematics
open PenroseIncidence PerjesConventions TwistorKinematicTensor
open scoped BigOperators Matrix

abbrev Columns (ι : Type*) := Matrix (Fin 4) ι ℂ

def conjugateEntries {m n : Type*} (A : Matrix m n ℂ) : Matrix m n ℂ :=
  fun i j => star (A i j)

@[simp] theorem conjugateEntries_twice {m n : Type*} (A : Matrix m n ℂ) :
    conjugateEntries (conjugateEntries A) = A := by ext i j; simp [conjugateEntries]

@[simp] theorem conjugateEntries_add {m n : Type*} (A B : Matrix m n ℂ) :
    conjugateEntries (A+B)=conjugateEntries A+conjugateEntries B := by
  ext i j; simp [conjugateEntries]

theorem conjugateEntries_mul {m n k : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n k ℂ) :
    conjugateEntries (A*B)=conjugateEntries A*conjugateEntries B := by
  ext i j
  simp [conjugateEntries, Matrix.mul_apply, star_mul, mul_comm]

@[simp] theorem conjugateEntries_conjTranspose {m n : Type*} (A : Matrix m n ℂ) :
    conjugateEntries A.conjTranspose=A.transpose := by
  ext i j; simp [conjugateEntries, Matrix.conjTranspose_apply]

@[simp] theorem conjugateEntries_one {ι : Type*} [DecidableEq ι] :
    conjugateEntries (1 : Matrix ι ι ℂ)=1 := by
  ext i j
  by_cases h : i=j <;> simp [conjugateEntries, Matrix.one_apply, h]

/-- I# followed by incidence-frame conjugation, expressed on actual four-coordinates. -/
def raisingMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,1; 0,0,-1,0; 0,0,0,0; 0,0,0,0]

def raisedColumns {ι : Type*} (X : Columns ι) : Columns ι :=
  raisingMatrix * conjugateEntries X

@[simp] theorem raisingMatrix_conjugate : conjugateEntries raisingMatrix=raisingMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [conjugateEntries, raisingMatrix]

theorem raisingMatrix_square_zero : raisingMatrix*raisingMatrix=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [raisingMatrix, Matrix.mul_apply, Fin.sum_univ_four]

@[simp] theorem raisedColumns_add {ι : Type*} (X Y : Columns ι) :
    raisedColumns (X+Y)=raisedColumns X+raisedColumns Y := by
  simp [raisedColumns, Matrix.mul_add]

theorem raisedColumns_mul {ι κ : Type*} [Fintype ι]
    (X : Columns ι) (U : Matrix ι κ ℂ) :
    raisedColumns (X*U)=raisedColumns X*conjugateEntries U := by
  rw [raisedColumns, conjugateEntries_mul, ← Matrix.mul_assoc]
  rfl

@[simp] theorem raisedColumns_twice {ι : Type*} (X : Columns ι) :
    raisedColumns (raisedColumns X)=0 := by
  unfold raisedColumns
  rw [conjugateEntries_mul, raisingMatrix_conjugate, conjugateEntries_twice,
    ← Matrix.mul_assoc, raisingMatrix_square_zero, Matrix.zero_mul]

def columns {ι : Type*} (Z : ι → Twistor4) : Columns ι :=
  fun a i => coordinateEquiv (Z i) a

theorem raisedColumns_column {ι : Type*} (Z : ι → Twistor4) (i : ι) :
    (fun a => raisedColumns (columns Z) a i) = coordinateEquiv (raised (Z i)) := by
  funext a
  fin_cases a <;>
    simp [raisedColumns, raisingMatrix, conjugateEntries, columns, coordinateEquiv,
      Matrix.mul_apply, Fin.sum_univ_four]

variable {ι : Type*} [Fintype ι]

/-- The total of Perjes (6.7), not a new independent particle carrier. -/
def totalKinematic (X : Columns ι) : Matrix (Fin 4) (Fin 4) ℂ :=
  X*(raisedColumns X).transpose+raisedColumns X*X.transpose

theorem totalKinematic_symmetric (X : Columns ι) :
    (totalKinematic X).transpose=totalKinematic X := by
  simp [totalKinematic, Matrix.transpose_add, Matrix.transpose_mul, add_comm]

theorem totalKinematic_eq_sum (Z : ι → Twistor4) :
    totalKinematic (columns Z)=∑ i, kinematic (Z i) := by
  ext a b
  simp only [totalKinematic, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have ha := congrFun (raisedColumns_column Z i) a
  have hb := congrFun (raisedColumns_column Z i) b
  rw [ha, hb]
  rfl

def lowerColumns (X : Columns ι) : Matrix (Fin 2) ι ℂ :=
  fun a i => ![X 2 i, X 3 i] a

def totalMomentum (X : Columns ι) : ComplexSpacetime :=
  lowerColumns X * (lowerColumns X).conjTranspose

theorem totalMomentum_positive (X : Columns ι) : (totalMomentum X).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem totalMomentum_readout (X : Columns ι) :
    momentumReadout (totalKinematic X)=totalMomentum X := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [momentumReadout, totalKinematic, totalMomentum, lowerColumns,
      raisedColumns, raisingMatrix, conjugateEntries, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_four, ← Finset.sum_neg_distrib]

/-- Total momentum really is the sum of the constituent null momenta. -/
theorem totalMomentum_eq_sum (Z : ι → Twistor4) :
    totalMomentum (columns Z)=∑ i, momentum (Z i).2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [totalMomentum, lowerColumns, columns, coordinateEquiv,
      momentum, Matrix.vecMulVec, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply]

/-- The already-proved outer-product mass formula is applied to actual constituents. -/
theorem two_constituent_mass_readout (Z W : Twistor4) :
    (totalMomentum (columns ![Z,W])).det =
      (Z.2 0 * W.2 1 - Z.2 1 * W.2 0) *
        star (Z.2 0 * W.2 1 - Z.2 1 * W.2 0) := by
  rw [totalMomentum_eq_sum, Fin.sum_univ_two]
  exact two_constituent_mass _ _

end InfoGeometry.Twistor.TwistorConstituentKinematics
