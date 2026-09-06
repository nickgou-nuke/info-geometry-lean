import proofs.D5ComplexMatrixRootSpaces

/-! # Rational isotropic-to-diagonal equivalence for complex `so(10)` -/

noncomputable section
set_option maxHeartbeats 1200000
namespace D5IsotropicDiagonalLieEquiv

open D5ComplexMatrixRootSpaces

def diagonalMetric : CM10
  | .inl i, .inl j => if i = j then 1 else 0
  | .inr i, .inr j => if i = j then -1 else 0
  | _, _ => 0

/-- Columns are the positive and negative vectors
`uᵢ + 1/2 vᵢ` and `uᵢ - 1/2 vᵢ`. -/
def isotropicBasisChange : CM10
  | .inl i, .inl j => if i = j then 1 else 0
  | .inl i, .inr j => if i = j then 1 else 0
  | .inr i, .inl j => if i = j then (1 / 2 : ℂ) else 0
  | .inr i, .inr j => if i = j then (-1 / 2 : ℂ) else 0

def isotropicBasisChangeInv : CM10
  | .inl i, .inl j => if i = j then (1 / 2 : ℂ) else 0
  | .inl i, .inr j => if i = j then 1 else 0
  | .inr i, .inl j => if i = j then (1 / 2 : ℂ) else 0
  | .inr i, .inr j => if i = j then -1 else 0

theorem basisChangeInv_mul :
    isotropicBasisChangeInv * isotropicBasisChange = 1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [isotropicBasisChangeInv, isotropicBasisChange, Matrix.mul_apply,
      Matrix.one_apply]
  all_goals by_cases h : a = b <;> simp [h] <;> norm_num

theorem basisChange_mul_inv :
    isotropicBasisChange * isotropicBasisChangeInv = 1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [isotropicBasisChangeInv, isotropicBasisChange, Matrix.mul_apply,
      Matrix.one_apply]
  all_goals by_cases h : a = b <;> simp [h] <;> norm_num

theorem metric_congruence :
    isotropicBasisChange.transpose * splitMetric * isotropicBasisChange =
      diagonalMetric := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [isotropicBasisChange, splitMetric, diagonalMetric, Matrix.mul_apply]
  all_goals by_cases h : a = b <;> simp [h] <;> norm_num

def isotropicSO10Submodule : Submodule ℂ CM10 :=
  { carrier := {A | IsSplitOrthogonal A}
    zero_mem' := by simp [IsSplitOrthogonal]
    add_mem' := by
      intro A B hA hB
      change IsSplitOrthogonal (A + B)
      simp only [IsSplitOrthogonal, Matrix.transpose_add, add_mul, mul_add]
      calc
        (A.transpose * splitMetric + B.transpose * splitMetric) +
            (splitMetric * A + splitMetric * B) =
          (A.transpose * splitMetric + splitMetric * A) +
            (B.transpose * splitMetric + splitMetric * B) := by abel
        _ = 0 := by rw [hA, hB]; simp
    smul_mem' := by
      intro c A hA
      change IsSplitOrthogonal (c • A)
      simp only [IsSplitOrthogonal, Matrix.transpose_smul, Matrix.smul_mul,
        Matrix.mul_smul]
      rw [← smul_add, hA, smul_zero] }

def isotropicSO10 : LieSubalgebra ℂ CM10 :=
  LieSubalgebra.mk isotropicSO10Submodule (by
      intro A B hA hB
      change IsSplitOrthogonal (A * B - B * A)
      simp only [IsSplitOrthogonal, Matrix.transpose_sub, Matrix.transpose_mul,
        mul_sub, sub_mul]
      have hAt : A.transpose * splitMetric = -(splitMetric * A) :=
        eq_neg_of_add_eq_zero_left hA
      have hBt : B.transpose * splitMetric = -(splitMetric * B) :=
        eq_neg_of_add_eq_zero_left hB
      rw [Matrix.mul_assoc B.transpose A.transpose splitMetric,
        Matrix.mul_assoc A.transpose B.transpose splitMetric, hAt, hBt]
      simp only [mul_neg]
      rw [← Matrix.mul_assoc B.transpose splitMetric A,
        ← Matrix.mul_assoc A.transpose splitMetric B, hBt, hAt]
      noncomm_ring)

def diagonalSO10Submodule : Submodule ℂ CM10 :=
  { carrier := {A | A.transpose * diagonalMetric + diagonalMetric * A = 0}
    zero_mem' := by simp
    add_mem' := by
      intro A B hA hB
      change (A + B).transpose * diagonalMetric + diagonalMetric * (A + B) = 0
      simp only [Matrix.transpose_add, add_mul, mul_add]
      calc
        (A.transpose * diagonalMetric + B.transpose * diagonalMetric) +
            (diagonalMetric * A + diagonalMetric * B) =
          (A.transpose * diagonalMetric + diagonalMetric * A) +
            (B.transpose * diagonalMetric + diagonalMetric * B) := by abel
        _ = 0 := by rw [hA, hB]; simp
    smul_mem' := by
      intro c A hA
      change (c • A).transpose * diagonalMetric + diagonalMetric * (c • A) = 0
      simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
      rw [← smul_add, hA, smul_zero] }

def diagonalSO10 : LieSubalgebra ℂ CM10 :=
  LieSubalgebra.mk diagonalSO10Submodule (by
      intro A B hA hB
      change (A * B - B * A).transpose * diagonalMetric +
        diagonalMetric * (A * B - B * A) = 0
      simp only [Matrix.transpose_sub, Matrix.transpose_mul, mul_sub, sub_mul]
      have hAt : A.transpose * diagonalMetric = -(diagonalMetric * A) :=
        eq_neg_of_add_eq_zero_left hA
      have hBt : B.transpose * diagonalMetric = -(diagonalMetric * B) :=
        eq_neg_of_add_eq_zero_left hB
      rw [Matrix.mul_assoc B.transpose A.transpose diagonalMetric,
        Matrix.mul_assoc A.transpose B.transpose diagonalMetric, hAt, hBt]
      simp only [mul_neg]
      rw [← Matrix.mul_assoc B.transpose diagonalMetric A,
        ← Matrix.mul_assoc A.transpose diagonalMetric B, hBt, hAt]
      noncomm_ring)

def conjugateToDiagonal (A : CM10) : CM10 :=
  isotropicBasisChangeInv * A * isotropicBasisChange

def conjugateToIsotropic (A : CM10) : CM10 :=
  isotropicBasisChange * A * isotropicBasisChangeInv

theorem conjugateToDiagonal_preserves {A : CM10} (hA : IsSplitOrthogonal A) :
    (conjugateToDiagonal A).transpose * diagonalMetric +
      diagonalMetric * conjugateToDiagonal A = 0 := by
  rw [← metric_congruence]
  simp only [conjugateToDiagonal, Matrix.transpose_mul, Matrix.mul_assoc]
  have hT : isotropicBasisChangeInv.transpose *
      isotropicBasisChange.transpose = 1 := by
    rw [← Matrix.transpose_mul, basisChange_mul_inv, Matrix.transpose_one]
  rw [← Matrix.mul_assoc isotropicBasisChangeInv.transpose
    isotropicBasisChange.transpose, hT, one_mul]
  rw [← Matrix.mul_assoc isotropicBasisChange isotropicBasisChangeInv,
    basisChange_mul_inv, one_mul]
  calc
    _ = isotropicBasisChange.transpose *
        (A.transpose * splitMetric + splitMetric * A) *
          isotropicBasisChange := by noncomm_ring
    _ = 0 := by rw [hA]; simp

theorem conjugateToIsotropic_preserves {A : CM10}
    (hA : A.transpose * diagonalMetric + diagonalMetric * A = 0) :
    IsSplitOrthogonal (conjugateToIsotropic A) := by
  have hmetric : isotropicBasisChangeInv.transpose * diagonalMetric *
      isotropicBasisChangeInv = splitMetric := by
    rw [← metric_congruence]
    simp only [Matrix.mul_assoc]
    have hT : isotropicBasisChangeInv.transpose *
        isotropicBasisChange.transpose = 1 := by
      rw [← Matrix.transpose_mul, basisChange_mul_inv, Matrix.transpose_one]
    rw [← Matrix.mul_assoc isotropicBasisChangeInv.transpose
      isotropicBasisChange.transpose, hT, one_mul]
    rw [basisChange_mul_inv, mul_one]
  change (isotropicBasisChange * A * isotropicBasisChangeInv).transpose *
      splitMetric + splitMetric *
        (isotropicBasisChange * A * isotropicBasisChangeInv) = 0
  rw [← hmetric]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  calc
    _ = isotropicBasisChangeInv.transpose *
        (A.transpose * diagonalMetric + diagonalMetric * A) *
          isotropicBasisChangeInv := by
            have hT : isotropicBasisChange.transpose *
                isotropicBasisChangeInv.transpose = 1 := by
              rw [← Matrix.transpose_mul, basisChangeInv_mul,
                Matrix.transpose_one]
            have hTc (X : CM10) : isotropicBasisChange.transpose *
                (isotropicBasisChangeInv.transpose * X) = X := by
              rw [← Matrix.mul_assoc, hT, one_mul]
            have hC (X : CM10) : isotropicBasisChangeInv *
                (isotropicBasisChange * X) = X := by
              rw [← Matrix.mul_assoc, basisChangeInv_mul, one_mul]
            simp_rw [hTc, hC]
            noncomm_ring
    _ = 0 := by rw [hA]; simp

def isotropicToDiagonal : isotropicSO10 →ₗ[ℂ] diagonalSO10 where
  toFun A := ⟨conjugateToDiagonal A, conjugateToDiagonal_preserves A.property⟩
  map_add' A B := by apply Subtype.ext; simp [conjugateToDiagonal, mul_add, add_mul]
  map_smul' c A := by
    apply Subtype.ext
    simp [conjugateToDiagonal]

def diagonalToIsotropic : diagonalSO10 →ₗ[ℂ] isotropicSO10 where
  toFun A := ⟨conjugateToIsotropic A, conjugateToIsotropic_preserves A.property⟩
  map_add' A B := by apply Subtype.ext; simp [conjugateToIsotropic, mul_add, add_mul]
  map_smul' c A := by
    apply Subtype.ext
    simp [conjugateToIsotropic]

theorem leftInverse : Function.LeftInverse diagonalToIsotropic isotropicToDiagonal := by
  intro A
  apply Subtype.ext
  change isotropicBasisChange *
    (isotropicBasisChangeInv * A.1 * isotropicBasisChange) *
      isotropicBasisChangeInv = A.1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc isotropicBasisChange isotropicBasisChangeInv,
    basisChange_mul_inv, one_mul, mul_one]

theorem rightInverse : Function.RightInverse diagonalToIsotropic isotropicToDiagonal := by
  intro A
  apply Subtype.ext
  change isotropicBasisChangeInv *
    (isotropicBasisChange * A.1 * isotropicBasisChangeInv) *
      isotropicBasisChange = A.1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc isotropicBasisChangeInv isotropicBasisChange,
    basisChangeInv_mul, one_mul, mul_one]

theorem isotropicToDiagonal_lie (A B : isotropicSO10) :
    isotropicToDiagonal ⁅A, B⁆ =
      ⁅isotropicToDiagonal A, isotropicToDiagonal B⁆ := by
  apply Subtype.ext
  change isotropicBasisChangeInv * (A.1 * B.1 - B.1 * A.1) *
      isotropicBasisChange =
    (isotropicBasisChangeInv * A.1 * isotropicBasisChange) *
      (isotropicBasisChangeInv * B.1 * isotropicBasisChange) -
    (isotropicBasisChangeInv * B.1 * isotropicBasisChange) *
      (isotropicBasisChangeInv * A.1 * isotropicBasisChange)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc isotropicBasisChange isotropicBasisChangeInv,
    basisChange_mul_inv, one_mul]
  rw [← Matrix.mul_assoc isotropicBasisChange isotropicBasisChangeInv,
    basisChange_mul_inv, one_mul]
  noncomm_ring

def isotropicDiagonalLieEquiv : isotropicSO10 ≃ₗ⁅ℂ⁆ diagonalSO10 :=
  LieEquiv.ofBijective
    { toLinearMap := isotropicToDiagonal
      map_lie' := fun {x y} => isotropicToDiagonal_lie x y }
    ⟨leftInverse.injective, fun y => ⟨diagonalToIsotropic y, rightInverse y⟩⟩

end D5IsotropicDiagonalLieEquiv
end noncomputable section
