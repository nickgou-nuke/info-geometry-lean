import proofs.SO55MetricCongruence

/-! # Lie equivalence between hyperbolic and diagonal `so(5,5)` models -/

noncomputable section
namespace SO55HyperbolicDiagonalLieEquiv

open SplitOctonionTKK55
open SplitOctonionTKK55Blocks
open SplitOctonionTKK55LieEquivalence
open HIndexFin10Reindex
open SO55RationalDiagonalization
open SO55MetricCongruence

def diagonalSO55Submodule : Submodule ℝ M10 where
  carrier := {A | A.transpose * eta55 + eta55 * A = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change (A + B).transpose * eta55 + eta55 * (A + B) = 0
    simp only [Matrix.transpose_add, add_mul, mul_add]
    calc
      (A.transpose * eta55 + B.transpose * eta55) +
          (eta55 * A + eta55 * B) =
        (A.transpose * eta55 + eta55 * A) +
          (B.transpose * eta55 + eta55 * B) := by abel
      _ = 0 := by rw [hA, hB]; simp
  smul_mem' := by
    intro c A hA
    change (c • A).transpose * eta55 + eta55 * (c • A) = 0
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add, hA, smul_zero]

def diagonalSO55 : LieSubalgebra ℝ M10 :=
  LieSubalgebra.mk diagonalSO55Submodule (by
    intro A B hA hB
    change (A * B - B * A).transpose * eta55 +
      eta55 * (A * B - B * A) = 0
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
    have hAt : A.transpose * eta55 = -(eta55 * A) :=
      eq_neg_of_add_eq_zero_left hA
    have hBt : B.transpose * eta55 = -(eta55 * B) :=
      eq_neg_of_add_eq_zero_left hB
    simp only [mul_sub, sub_mul]
    rw [Matrix.mul_assoc B.transpose A.transpose eta55,
      Matrix.mul_assoc A.transpose B.transpose eta55, hAt, hBt]
    simp only [mul_neg]
    rw [← Matrix.mul_assoc B.transpose eta55 A,
      ← Matrix.mul_assoc A.transpose eta55 B, hBt, hAt]
    noncomm_ring)

private def reindexAlg : HMatrix ≃ₐ[ℝ] M10 :=
  Matrix.reindexAlgEquiv ℝ ℝ hIndexEquivFin10

theorem reindexAlg_apply (A : HMatrix) : reindexAlg A = reindexHMatrix A := rfl

theorem reindex_hyperbolic_constraint {A : HMatrix}
    (hA : A.transpose * metric55 + metric55 * A = 0) :
    (reindexHMatrix A).transpose * hyperbolicMetric10 +
      hyperbolicMetric10 * reindexHMatrix A = 0 := by
  change (reindexAlg A).transpose * reindexAlg metric55 +
      reindexAlg metric55 * reindexAlg A = 0
  rw [show (reindexAlg A).transpose = reindexAlg A.transpose by
    exact Matrix.transpose_reindex hIndexEquivFin10 hIndexEquivFin10 A]
  change reindexAlg (A.transpose * metric55 + metric55 * A) = 0
  rw [hA, map_zero]

def conjugateToDiagonalMatrix (A : HMatrix) : M10 :=
  basisChangeInv * reindexHMatrix A * basisChange

def conjugateToHyperbolicMatrix (B : M10) : HMatrix :=
  unreindexHMatrix (basisChange * B * basisChangeInv)

theorem conjugateToDiagonal_preserves_constraint {A : HMatrix}
    (hA : A.transpose * metric55 + metric55 * A = 0) :
    (conjugateToDiagonalMatrix A).transpose * eta55 +
      eta55 * conjugateToDiagonalMatrix A = 0 := by
  have horth := reindex_hyperbolic_constraint hA
  have hmetric := basisChange_metric_congruence
  have hleft := basisChangeInv_mul
  have hright := basisChange_mul_inv
  have hrightT : basisChangeInv.transpose * basisChange.transpose = 1 := by
    rw [← Matrix.transpose_mul, hright, Matrix.transpose_one]
  simp only [conjugateToDiagonalMatrix, Matrix.transpose_mul]
  rw [← hmetric]
  calc
    _ =
      basisChange.transpose *
        ((reindexHMatrix A).transpose * hyperbolicMetric10 +
          hyperbolicMetric10 * reindexHMatrix A) * basisChange := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc basisChangeInv.transpose basisChange.transpose,
          hrightT, one_mul]
        rw [← Matrix.mul_assoc basisChange basisChangeInv, hright, one_mul]
        noncomm_ring
    _ = 0 := by rw [horth]; simp

theorem basisChangeInv_metric_congruence :
    basisChangeInv.transpose * eta55 * basisChangeInv = hyperbolicMetric10 := by
  rw [← basisChange_metric_congruence]
  have hright := basisChange_mul_inv
  have hrightT : basisChangeInv.transpose * basisChange.transpose = 1 := by
    rw [← Matrix.transpose_mul, hright, Matrix.transpose_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc basisChangeInv.transpose basisChange.transpose,
    hrightT, one_mul]
  rw [hright, mul_one]

theorem conjugateToHyperbolic10_preserves_constraint {B : M10}
    (hB : B.transpose * eta55 + eta55 * B = 0) :
    (basisChange * B * basisChangeInv).transpose * hyperbolicMetric10 +
      hyperbolicMetric10 * (basisChange * B * basisChangeInv) = 0 := by
  have hmetric := basisChangeInv_metric_congruence
  have hleft := basisChangeInv_mul
  have hleftT : basisChange.transpose * basisChangeInv.transpose = 1 := by
    rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
  rw [← hmetric]
  simp only [Matrix.transpose_mul]
  calc
    _ = basisChangeInv.transpose *
        (B.transpose * eta55 + eta55 * B) * basisChangeInv := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc basisChange.transpose basisChangeInv.transpose,
        hleftT, one_mul]
      rw [← Matrix.mul_assoc basisChangeInv basisChange, hleft, one_mul]
      noncomm_ring
    _ = 0 := by rw [hB]; simp

theorem unreindex_preserves_constraint {B : M10}
    (hB : B.transpose * hyperbolicMetric10 + hyperbolicMetric10 * B = 0) :
    (unreindexHMatrix B).transpose * metric55 +
      metric55 * unreindexHMatrix B = 0 := by
  apply reindexAlg.injective
  change reindexAlg ((unreindexHMatrix B).transpose * metric55 +
      metric55 * unreindexHMatrix B) = reindexAlg 0
  rw [map_add, map_mul, map_mul, map_zero]
  rw [show reindexAlg (unreindexHMatrix B).transpose = B.transpose by
    rw [show reindexAlg (unreindexHMatrix B).transpose =
        (reindexAlg (unreindexHMatrix B)).transpose by
      exact (Matrix.transpose_reindex hIndexEquivFin10 hIndexEquivFin10
        (unreindexHMatrix B)).symm]
    change (reindexHMatrix (unreindexHMatrix B)).transpose = B.transpose
    rw [reindex_unreindex]]
  change B.transpose * reindexAlg metric55 +
      reindexAlg metric55 * reindexAlg (unreindexHMatrix B) = 0
  change B.transpose * hyperbolicMetric10 +
      hyperbolicMetric10 * reindexHMatrix (unreindexHMatrix B) = 0
  rw [reindex_unreindex]
  exact hB

def hyperbolicToDiagonal : hyperbolicSO55 →ₗ[ℝ] diagonalSO55 where
  toFun A := ⟨conjugateToDiagonalMatrix A.1,
    conjugateToDiagonal_preserves_constraint A.2⟩
  map_add' A B := by
    apply Subtype.ext
    change basisChangeInv * reindexAlg (A.1 + B.1) * basisChange =
      basisChangeInv * reindexHMatrix A.1 * basisChange +
        basisChangeInv * reindexHMatrix B.1 * basisChange
    rw [map_add]
    change basisChangeInv * (reindexHMatrix A.1 + reindexHMatrix B.1) *
      basisChange = _
    rw [mul_add, add_mul]
  map_smul' c A := by
    apply Subtype.ext
    change basisChangeInv * reindexAlg (c • A.1) * basisChange =
      c • (basisChangeInv * reindexHMatrix A.1 * basisChange)
    rw [map_smul]
    change basisChangeInv * (c • reindexHMatrix A.1) * basisChange = _
    rw [Matrix.mul_smul, Matrix.smul_mul]

def diagonalToHyperbolic : diagonalSO55 →ₗ[ℝ] hyperbolicSO55 where
  toFun B := ⟨conjugateToHyperbolicMatrix B.1,
    unreindex_preserves_constraint
      (conjugateToHyperbolic10_preserves_constraint B.2)⟩
  map_add' A B := by
    apply Subtype.ext
    apply hMatrixFin10LinearEquiv.injective
    change reindexHMatrix (unreindexHMatrix
        (basisChange * (A.1 + B.1) * basisChangeInv)) =
      reindexHMatrix
        (unreindexHMatrix (basisChange * A.1 * basisChangeInv) +
          unreindexHMatrix (basisChange * B.1 * basisChangeInv))
    rw [reindex_unreindex]
    change basisChange * (A.1 + B.1) * basisChangeInv =
      reindexHMatrix (unreindexHMatrix (basisChange * A.1 * basisChangeInv)) +
        reindexHMatrix (unreindexHMatrix (basisChange * B.1 * basisChangeInv))
    rw [reindex_unreindex, reindex_unreindex]
    rw [mul_add, add_mul]
  map_smul' c A := by
    apply Subtype.ext
    apply hMatrixFin10LinearEquiv.injective
    change reindexHMatrix (unreindexHMatrix
        (basisChange * (c • A.1) * basisChangeInv)) =
      reindexHMatrix (c • unreindexHMatrix
        (basisChange * A.1 * basisChangeInv))
    rw [reindex_unreindex]
    change basisChange * (c • A.1) * basisChangeInv =
      c • reindexHMatrix (unreindexHMatrix
        (basisChange * A.1 * basisChangeInv))
    rw [reindex_unreindex]
    rw [Matrix.mul_smul, Matrix.smul_mul]

theorem hyperbolicToDiagonal_leftInverse :
    Function.LeftInverse diagonalToHyperbolic hyperbolicToDiagonal := by
  intro A
  apply Subtype.ext
  change unreindexHMatrix
      (basisChange * (basisChangeInv * reindexHMatrix A.1 * basisChange) *
        basisChangeInv) = A.1
  rw [← unreindex_reindex A.1]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc basisChange basisChangeInv,
    basisChange_mul_inv, one_mul]
  rw [reindex_unreindex, mul_one]

theorem hyperbolicToDiagonal_rightInverse :
    Function.RightInverse diagonalToHyperbolic hyperbolicToDiagonal := by
  intro B
  apply Subtype.ext
  change basisChangeInv *
      reindexHMatrix (unreindexHMatrix
        (basisChange * B.1 * basisChangeInv)) * basisChange = B.1
  rw [reindex_unreindex]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc basisChangeInv basisChange,
    basisChangeInv_mul, one_mul]
  rw [mul_one]

def hyperbolicDiagonalLinearEquiv : hyperbolicSO55 ≃ₗ[ℝ] diagonalSO55 where
  toLinearMap := hyperbolicToDiagonal
  invFun := diagonalToHyperbolic
  left_inv := hyperbolicToDiagonal_leftInverse
  right_inv := hyperbolicToDiagonal_rightInverse

theorem hyperbolicToDiagonal_lie (A B : hyperbolicSO55) :
    hyperbolicToDiagonal ⁅A, B⁆ =
      ⁅hyperbolicToDiagonal A, hyperbolicToDiagonal B⁆ := by
  apply Subtype.ext
  change basisChangeInv * reindexHMatrix (A.1 * B.1 - B.1 * A.1) *
      basisChange =
    (basisChangeInv * reindexHMatrix A.1 * basisChange) *
        (basisChangeInv * reindexHMatrix B.1 * basisChange) -
      (basisChangeInv * reindexHMatrix B.1 * basisChange) *
        (basisChangeInv * reindexHMatrix A.1 * basisChange)
  change basisChangeInv * reindexAlg (A.1 * B.1 - B.1 * A.1) *
      basisChange = _
  rw [map_sub, map_mul, map_mul]
  change basisChangeInv *
      (reindexHMatrix A.1 * reindexHMatrix B.1 -
        reindexHMatrix B.1 * reindexHMatrix A.1) * basisChange = _
  have h := basisChange_mul_inv
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc basisChange basisChangeInv, h, one_mul]
  rw [← Matrix.mul_assoc basisChange basisChangeInv, h, one_mul]
  noncomm_ring

def hyperbolicDiagonalLieHom : hyperbolicSO55 →ₗ⁅ℝ⁆ diagonalSO55 where
  toLinearMap := hyperbolicToDiagonal
  map_lie' := by
    intro A B
    exact hyperbolicToDiagonal_lie A B

def hyperbolicDiagonalLieEquiv : hyperbolicSO55 ≃ₗ⁅ℝ⁆ diagonalSO55 :=
  LieEquiv.ofBijective hyperbolicDiagonalLieHom
    ⟨by
      intro A B h
      exact hyperbolicToDiagonal_leftInverse.injective h,
     by
      intro B
      exact ⟨diagonalToHyperbolic B,
        hyperbolicToDiagonal_rightInverse B⟩⟩

/-- Final diagonal capstone obtained by composing the independently typed TKK
source with the rational hyperbolic-to-diagonal change of basis. -/
def tkkDiagonalLieEquiv : TKKBlockCarrier ≃ₗ⁅ℝ⁆ diagonalSO55 :=
  tkkHyperbolicLieEquiv.trans hyperbolicDiagonalLieEquiv

end SO55HyperbolicDiagonalLieEquiv
end noncomputable section
