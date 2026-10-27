import InfoGeometry.Twistor.TwistorConstituentKinematics

/-!
# Unitary mixing and skew infinity shifts of constituent twistors

The two ingredients of Perjes (6.14) act on the same constituent carrier.
Their invariant is constructed, not supplied as a structure field. No particle
classification or identification of the entire stabilizer with ISU(3) is asserted.
-/
noncomputable section
namespace InfoGeometry.Twistor.TwistorInternalSymmetry
open TwistorConstituentKinematics
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def skewShift (Λ : Matrix ι ι ℂ) (X : Columns ι) : Columns ι :=
  X+raisedColumns X*Λ

@[simp] theorem raised_skewShift (Λ : Matrix ι ι ℂ) (X : Columns ι) :
    raisedColumns (skewShift Λ X)=raisedColumns X := by
  rw [skewShift, raisedColumns_add, raisedColumns_mul, raisedColumns_twice]
  simp

theorem skewShift_add (Λ Μ : Matrix ι ι ℂ) (X : Columns ι) :
    skewShift Λ (skewShift Μ X)=skewShift (Μ+Λ) X := by
  simp [skewShift, Matrix.mul_add]
  abel

theorem totalKinematic_skewShift (Λ : Matrix ι ι ℂ) (hΛ : Λ.transpose = -Λ)
    (X : Columns ι) : totalKinematic (skewShift Λ X)=totalKinematic X := by
  have hz : (raisedColumns X*Λ)*(raisedColumns X).transpose +
      raisedColumns X*(raisedColumns X*Λ).transpose=0 := by
    rw [Matrix.transpose_mul, hΛ, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, add_neg_cancel]
  unfold totalKinematic
  rw [raised_skewShift]
  simp only [skewShift, Matrix.add_mul, Matrix.transpose_add, Matrix.mul_add]
  calc
    X*(raisedColumns X).transpose+(raisedColumns X*Λ)*(raisedColumns X).transpose+
        (raisedColumns X*X.transpose+raisedColumns X*(raisedColumns X*Λ).transpose) =
      (X*(raisedColumns X).transpose+raisedColumns X*X.transpose)+
        ((raisedColumns X*Λ)*(raisedColumns X).transpose+
          raisedColumns X*(raisedColumns X*Λ).transpose) := by abel
    _ = X*(raisedColumns X).transpose+raisedColumns X*X.transpose := by rw [hz,add_zero]

theorem totalKinematic_unitary (U : Matrix ι ι ℂ)
    (hU : U*U.conjTranspose=1) (X : Columns ι) :
    totalKinematic (X*U)=totalKinematic X := by
  have hc : conjugateEntries U * U.transpose=1 := by
    have h := congrArg conjugateEntries hU
    simpa [conjugateEntries_mul] using h
  have ht : (conjugateEntries U).transpose=U.conjTranspose := by ext i j; rfl
  unfold totalKinematic
  rw [raisedColumns_mul, Matrix.transpose_mul, Matrix.transpose_mul, ht]
  calc
    X*U*(U.conjTranspose*(raisedColumns X).transpose) +
        raisedColumns X*conjugateEntries U*(U.transpose*X.transpose) =
      X*(U*U.conjTranspose)*(raisedColumns X).transpose +
        raisedColumns X*(conjugateEntries U*U.transpose)*X.transpose := by
          simp only [Matrix.mul_assoc]
    _ = X*(raisedColumns X).transpose+raisedColumns X*X.transpose := by rw [hU,hc]; simp

def internalTransform (U Λ : Matrix ι ι ℂ) (X : Columns ι) : Columns ι :=
  skewShift Λ X * U

theorem internalTransform_preserves_kinematics (U Λ : Matrix ι ι ℂ)
    (hU : U*U.conjTranspose=1) (hΛ : Λ.transpose = -Λ) (X : Columns ι) :
    totalKinematic (internalTransform U Λ X)=totalKinematic X := by
  rw [internalTransform, totalKinematic_unitary U hU, totalKinematic_skewShift Λ hΛ]

theorem internalTransform_preserves_momentum (U Λ : Matrix ι ι ℂ)
    (hU : U*U.conjTranspose=1) (hΛ : Λ.transpose = -Λ) (X : Columns ι) :
    totalMomentum (internalTransform U Λ X)=totalMomentum X := by
  rw [← totalMomentum_readout, internalTransform_preserves_kinematics U Λ hU hΛ,
    totalMomentum_readout]

theorem internalTransform_preserves_mass (U Λ : Matrix ι ι ℂ)
    (hU : U*U.conjTranspose=1) (hΛ : Λ.transpose = -Λ) (X : Columns ι) :
    (totalMomentum (internalTransform U Λ X)).det=(totalMomentum X).det := by
  rw [internalTransform_preserves_momentum U Λ hU hΛ]

def skewShiftEquiv (Λ : Matrix ι ι ℂ) : Columns ι ≃ₗ[ℝ] Columns ι where
  toFun := skewShift Λ
  invFun := skewShift (-Λ)
  left_inv X := by rw [skewShift_add]; simp [skewShift]
  right_inv X := by rw [skewShift_add]; simp [skewShift]
  map_add' X Y := by simp [skewShift, Matrix.add_mul]; abel
  map_smul' r X := by
    ext i j
    fin_cases i <;>
      simp [skewShift, raisedColumns, raisingMatrix, conjugateEntries,
        Matrix.mul_apply, Fin.sum_univ_four, Finset.mul_sum, Finset.sum_mul,
        smul_eq_mul, star_mul, mul_add, mul_assoc]

def unitaryMixEquiv (U : Matrix.unitaryGroup ι ℂ) : Columns ι ≃ₗ[ℝ] Columns ι where
  toFun X := X*(U : Matrix ι ι ℂ)
  invFun X := X*(U : Matrix ι ι ℂ).conjTranspose
  left_inv X := by rw [Matrix.mul_assoc, U.property.2]; simp
  right_inv X := by rw [Matrix.mul_assoc, U.property.1]; simp
  map_add' X Y := Matrix.add_mul _ _ _
  map_smul' r X := by simp [Matrix.smul_mul]

/-- Actual stabilizer subgroup, with no assumed classification. -/
def kinematicStabilizer : Subgroup (Columns ι ≃ₗ[ℝ] Columns ι) where
  carrier := {g | ∀ X, totalKinematic (g X)=totalKinematic X}
  one_mem' := by intro X; rfl
  mul_mem' := by intro g h hg hh X; exact (hg (h X)).trans (hh X)
  inv_mem' := by
    intro g hg X
    have h := hg (g.symm X)
    simpa using h.symm

theorem skewShift_mem_stabilizer (Λ : Matrix ι ι ℂ) (hΛ : Λ.transpose = -Λ) :
    skewShiftEquiv Λ ∈ kinematicStabilizer := totalKinematic_skewShift Λ hΛ

theorem unitaryMix_mem_stabilizer (U : Matrix.unitaryGroup ι ℂ) :
    unitaryMixEquiv U ∈ kinematicStabilizer := totalKinematic_unitary _ U.property.2

end InfoGeometry.Twistor.TwistorInternalSymmetry
