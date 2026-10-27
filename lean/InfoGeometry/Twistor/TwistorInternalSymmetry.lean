import InfoGeometry.Twistor.TwistorConstituentKinematics

/-!
# Concrete internal transformations of constituent twistors

Perjes (6.14) contains both unitary mixing and a skew-complex shift through
the infinity tensor. Both transformations below act on the same finite
family of native twistors, and preserve its actual total kinematic tensor.
Columns act on the right; all matrix product orders are retained. No
classification as ISU(3), nor particle multiplet identification, is inferred.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwistorInternalSymmetry

open Matrix
open scoped BigOperators
open PenroseIncidence TwistorKinematicTensor TwistorConstituentKinematics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateColumns (Z : ι → Twistor4) : Matrix TwistorIndex ι ℂ :=
  fun a i => twistorCoordinate (Z i) a

def raisedColumns (Z : ι → Twistor4) : Matrix TwistorIndex ι ℂ :=
  coordinateColumns (fun i => raisedConjugate (Z i))

/-- Entrywise conjugation is not the matrix star (conjugate transpose). -/
def entryConjugate (U : Matrix ι ι ℂ) : Matrix ι ι ℂ := fun i j => star (U i j)

@[simp] theorem entryConjugate_transpose (U : Matrix ι ι ℂ) :
    (entryConjugate U)ᵀ = Uᴴ := rfl

@[simp] theorem twistorCoordinate_sum (Z : ι → Twistor4) (a : TwistorIndex) :
    twistorCoordinate (∑ i, Z i) a = ∑ i, twistorCoordinate (Z i) a := by
  cases a <;> simp [twistorCoordinate]

@[simp] theorem raisedConjugate_sum (Z : ι → Twistor4) :
    raisedConjugate (∑ i, Z i) = ∑ i, raisedConjugate (Z i) := by
  apply Prod.ext <;> funext a <;> fin_cases a <;>
    simp [raisedConjugate_explicit]

theorem coordinateColumns_injective : Function.Injective (coordinateColumns (ι := ι)) := by
  intro Z W h
  funext i
  apply Prod.ext <;> funext a
  · exact congrArg (fun M => M (Sum.inl a) i) h
  · exact congrArg (fun M => M (Sum.inr a) i) h

theorem totalKinematic_matrix_formula (Z : ι → Twistor4) :
    totalKinematic Z = coordinateColumns Z * (raisedColumns Z)ᵀ +
      raisedColumns Z * (coordinateColumns Z)ᵀ := by
  ext a b
  simp [totalKinematic, kinematic, coordinateColumns, raisedColumns,
    Matrix.mul_apply, vecMulVec, Finset.sum_add_distrib]

/-- Right-column convention for the constituent unitary action. -/
def mix (U : Matrix ι ι ℂ) (Z : ι → Twistor4) : ι → Twistor4 :=
  fun j => ∑ i, U i j • Z i

theorem coordinateColumns_mix (U : Matrix ι ι ℂ) (Z : ι → Twistor4) :
    coordinateColumns (mix U Z) = coordinateColumns Z * U := by
  ext a j
  simp [coordinateColumns, mix, Matrix.mul_apply, twistorCoordinate_sum, mul_comm]

theorem raisedColumns_mix (U : Matrix ι ι ℂ) (Z : ι → Twistor4) :
    raisedColumns (mix U Z) = raisedColumns Z * entryConjugate U := by
  ext a j
  simp [raisedColumns, coordinateColumns, mix, Matrix.mul_apply, entryConjugate,
    twistorCoordinate_sum, mul_comm]

theorem spinorColumns_mix (U : Matrix ι ι ℂ) (Z : ι → Twistor4) :
    spinorColumns (mix U Z) = spinorColumns Z * U := by
  ext a j
  simp [spinorColumns, mix, Matrix.mul_apply, mul_comm]

theorem mix_composition (U V : Matrix ι ι ℂ) (Z : ι → Twistor4) :
    mix V (mix U Z) = mix (U * V) Z := by
  apply coordinateColumns_injective
  simp only [coordinateColumns_mix, Matrix.mul_assoc]

theorem unitary_momentum_invariant (U : Matrix ι ι ℂ)
    (hU : U * Uᴴ = 1) (Z : ι → Twistor4) :
    totalMomentum (mix U Z) = totalMomentum Z := by
  simp only [totalMomentum, spinorColumns_mix, Matrix.conjTranspose_mul]
  calc (spinorColumns Z * U) * (Uᴴ * (spinorColumns Z)ᴴ)
      = spinorColumns Z * (U * Uᴴ) * (spinorColumns Z)ᴴ := by simp [Matrix.mul_assoc]
    _ = spinorColumns Z * (spinorColumns Z)ᴴ := by rw [hU]; simp

theorem unitary_kinematic_invariant (U : Matrix ι ι ℂ)
    (hU : U * Uᴴ = 1) (Z : ι → Twistor4) :
    totalKinematic (mix U Z) = totalKinematic Z := by
  have hUc : entryConjugate U * Uᵀ = 1 := by
    simpa [Matrix.transpose_mul, entryConjugate] using congrArg Matrix.transpose hU
  simp only [totalKinematic_matrix_formula, coordinateColumns_mix, raisedColumns_mix,
    Matrix.transpose_mul, entryConjugate_transpose]
  have h1 : (coordinateColumns Z * U) * (Uᴴ * (raisedColumns Z)ᵀ) =
      coordinateColumns Z * (raisedColumns Z)ᵀ := by
    calc _ = coordinateColumns Z * (U * Uᴴ) * (raisedColumns Z)ᵀ := by simp [Matrix.mul_assoc]
         _ = _ := by rw [hU]; simp
  have h2 : (raisedColumns Z * entryConjugate U) * (Uᵀ * (coordinateColumns Z)ᵀ) =
      raisedColumns Z * (coordinateColumns Z)ᵀ := by
    calc _ = raisedColumns Z * (entryConjugate U * Uᵀ) * (coordinateColumns Z)ᵀ := by
                simp [Matrix.mul_assoc]
         _ = _ := by rw [hUc]; simp
  rw [h1, h2]

/-- The infinity-tensor shift, with no new independent constituent data. -/
def skewShift (L : Matrix ι ι ℂ) (Z : ι → Twistor4) : ι → Twistor4 :=
  fun j => Z j + ∑ i, L i j • raisedConjugate (Z i)

theorem raised_skewShift (L : Matrix ι ι ℂ) (Z : ι → Twistor4) (j : ι) :
    raisedConjugate (skewShift L Z j) = raisedConjugate (Z j) := by
  simp [skewShift]

theorem coordinateColumns_skewShift (L : Matrix ι ι ℂ) (Z : ι → Twistor4) :
    coordinateColumns (skewShift L Z) = coordinateColumns Z + raisedColumns Z * L := by
  ext a j
  simp [coordinateColumns, raisedColumns, skewShift, Matrix.mul_apply, mul_comm]

theorem raisedColumns_skewShift (L : Matrix ι ι ℂ) (Z : ι → Twistor4) :
    raisedColumns (skewShift L Z) = raisedColumns Z := by
  ext a j
  simp [raisedColumns, coordinateColumns, raised_skewShift]

theorem skewShift_momentum_invariant (L : Matrix ι ι ℂ) (Z : ι → Twistor4) :
    totalMomentum (skewShift L Z) = totalMomentum Z := by
  have hP : spinorColumns (skewShift L Z) = spinorColumns Z := by
    ext a j
    simp [spinorColumns, skewShift]
  simp only [totalMomentum, hP]

/-- The exact defect makes the skew-symmetry hypothesis inspectable. -/
theorem skewShift_kinematic_defect (L : Matrix ι ι ℂ) (Z : ι → Twistor4) :
    totalKinematic (skewShift L Z) - totalKinematic Z =
      raisedColumns Z * (L + Lᵀ) * (raisedColumns Z)ᵀ := by
  simp only [totalKinematic_matrix_formula, coordinateColumns_skewShift,
    raisedColumns_skewShift, Matrix.transpose_add, Matrix.transpose_mul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  abel

theorem skewShift_kinematic_invariant (L : Matrix ι ι ℂ)
    (hL : Lᵀ = -L) (Z : ι → Twistor4) :
    totalKinematic (skewShift L Z) = totalKinematic Z := by
  apply sub_eq_zero.mp
  rw [skewShift_kinematic_defect, hL]
  simp

/-- Both parts of (6.14), with their actual matrix hypotheses. -/
theorem internal_kinematic_invariant (U L : Matrix ι ι ℂ)
    (hU : U * Uᴴ = 1) (hL : Lᵀ = -L) (Z : ι → Twistor4) :
    totalKinematic (mix U (skewShift L Z)) = totalKinematic Z := by
  rw [unitary_kinematic_invariant U hU, skewShift_kinematic_invariant L hL]

end InfoGeometry.Twistor.TwistorInternalSymmetry
