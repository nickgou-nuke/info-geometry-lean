import InfoGeometry.Canonical.O55OrthogonalLieCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section
set_option maxHeartbeats 1000000

namespace InfoGeometry.Canonical.HyperbolicDiagonalO55

open Matrix
open InfoGeometry.Canonical.O55Representation

abbrev HMatrix := Matrix (Fin 10) (Fin 10) ℝ

def hyperbolicMetricMatrix : HMatrix := fun i j =>
  if i.val = 0 ∧ j.val = 9 then 2
  else if i.val = 9 ∧ j.val = 0 then 2
  else if 0 < i.val ∧ i.val < 9 ∧ i = j then
    if i.val ≤ 4 then 1 else -1
  else 0

def endpointChange : HMatrix := fun i j =>
  if i.val = 0 ∧ j.val = 0 then (1 / 2 : ℝ)
  else if i.val = 0 ∧ j.val = 9 then (1 / 2 : ℝ)
  else if i.val = 9 ∧ j.val = 0 then (1 / 2 : ℝ)
  else if i.val = 9 ∧ j.val = 9 then (-1 / 2 : ℝ)
  else if i = j ∧ 0 < i.val ∧ i.val < 9 then 1
  else 0

def endpointChangeInv : HMatrix := fun i j =>
  if i.val = 0 ∧ j.val = 0 then 1
  else if i.val = 0 ∧ j.val = 9 then 1
  else if i.val = 9 ∧ j.val = 0 then 1
  else if i.val = 9 ∧ j.val = 9 then (-1 : ℝ)
  else if i = j ∧ 0 < i.val ∧ i.val < 9 then 1
  else 0

theorem hyperbolicMetricMatrix_transpose :
    hyperbolicMetricMatrixᵀ = hyperbolicMetricMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicMetricMatrix, Matrix.transpose_apply]

theorem endpointChange_transpose : endpointChangeᵀ = endpointChange := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [endpointChange, Matrix.transpose_apply]

theorem endpointChangeInv_transpose : endpointChangeInvᵀ = endpointChangeInv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [endpointChangeInv, Matrix.transpose_apply]

theorem endpointChangeInv_mul : endpointChangeInv * endpointChange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [endpointChange, endpointChangeInv, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> norm_num

theorem endpointChange_mul_inv : endpointChange * endpointChangeInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [endpointChange, endpointChangeInv, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> norm_num

theorem endpointChange_metric_congruence :
    endpointChangeᵀ * hyperbolicMetricMatrix * endpointChange = O55Form := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [endpointChange, hyperbolicMetricMatrix, O55Form,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    norm_num

theorem endpointChange_transpose_mul_metric :
    endpointChangeᵀ * hyperbolicMetricMatrix * endpointChange = O55Form :=
  endpointChange_metric_congruence

def hyperbolicPredicate (A : HMatrix) : Prop :=
  Aᵀ * hyperbolicMetricMatrix + hyperbolicMetricMatrix * A = 0

def hyperbolicSubmodule : Submodule ℝ HMatrix where
  carrier := {A | hyperbolicPredicate A}
  zero_mem' := by simp [hyperbolicPredicate]
  add_mem' := by
    intro A B hA hB
    change Aᵀ * hyperbolicMetricMatrix + hyperbolicMetricMatrix * A = 0 at hA
    change Bᵀ * hyperbolicMetricMatrix + hyperbolicMetricMatrix * B = 0 at hB
    change (A + B)ᵀ * hyperbolicMetricMatrix +
      hyperbolicMetricMatrix * (A + B) = 0
    rw [Matrix.transpose_add, add_mul, mul_add]
    calc
      Aᵀ * hyperbolicMetricMatrix + Bᵀ * hyperbolicMetricMatrix +
          (hyperbolicMetricMatrix * A + hyperbolicMetricMatrix * B) =
        (Aᵀ * hyperbolicMetricMatrix + hyperbolicMetricMatrix * A) +
          (Bᵀ * hyperbolicMetricMatrix + hyperbolicMetricMatrix * B) := by
            abel
      _ = 0 := by rw [hA, hB]; simp
  smul_mem' := by
    intro r A hA
    change (r • A)ᵀ * hyperbolicMetricMatrix +
      hyperbolicMetricMatrix * (r • A) = 0
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      ← smul_add, hA, smul_zero]

def HyperbolicOrthogonal := hyperbolicSubmodule

def hyperbolicToDiagonal (A : HMatrix) : HMatrix :=
  endpointChangeInv * A * endpointChange

def diagonalToHyperbolic (A : HMatrix) : HMatrix :=
  endpointChange * A * endpointChangeInv

theorem hyperbolicPredicate_commutator {A B : HMatrix}
    (hA : hyperbolicPredicate A) (hB : hyperbolicPredicate B) :
    hyperbolicPredicate (A * B - B * A) := by
  have hA' : Aᵀ * hyperbolicMetricMatrix =
      -(hyperbolicMetricMatrix * A) :=
    eq_neg_of_add_eq_zero_left hA
  have hB' : Bᵀ * hyperbolicMetricMatrix =
      -(hyperbolicMetricMatrix * B) :=
    eq_neg_of_add_eq_zero_left hB
  change (A * B - B * A)ᵀ * hyperbolicMetricMatrix +
      hyperbolicMetricMatrix * (A * B - B * A) = 0
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    sub_mul, mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hA', hB']
  simp only [mul_neg, sub_eq_add_neg]
  rw [← Matrix.mul_assoc Bᵀ hyperbolicMetricMatrix A,
    ← Matrix.mul_assoc Aᵀ hyperbolicMetricMatrix B]
  rw [hB', hA']
  simp only [neg_mul, neg_neg]
  rw [← Matrix.mul_assoc hyperbolicMetricMatrix A B,
    ← Matrix.mul_assoc hyperbolicMetricMatrix B A]
  abel

def hyperbolicLieSubalgebra : LieSubalgebra ℝ HMatrix :=
  { hyperbolicSubmodule with
    lie_mem' := by
      intro A B hA hB
      exact hyperbolicPredicate_commutator hA hB }

def HyperbolicOrthogonalLie := hyperbolicLieSubalgebra

def diagonalToHyperbolicInv (A : HMatrix) : HMatrix :=
  endpointChange * A * endpointChangeInv

theorem endpointChangeInv_metric_congruence :
    endpointChangeInvᵀ * O55Form * endpointChangeInv =
      hyperbolicMetricMatrix := by
  rw [endpointChangeInv_transpose, ← endpointChange_metric_congruence,
    endpointChange_transpose]
  calc
    endpointChangeInv * (endpointChange * hyperbolicMetricMatrix * endpointChange) *
          endpointChangeInv =
        (endpointChangeInv * endpointChange) * hyperbolicMetricMatrix *
          (endpointChange * endpointChangeInv) := by
            noncomm_ring
    _ = hyperbolicMetricMatrix := by
      simp only [endpointChangeInv_mul,
        endpointChange_mul_inv, Matrix.one_mul, Matrix.mul_one]

theorem hyperbolicToDiagonal_preserves_constraint {A : HMatrix}
    (hA : hyperbolicPredicate A) :
    (hyperbolicToDiagonal A)ᵀ * O55Form +
      O55Form * hyperbolicToDiagonal A = 0 := by
  rw [hyperbolicToDiagonal, Matrix.transpose_mul, Matrix.transpose_mul,
    endpointChange_transpose, endpointChangeInv_transpose,
    ← endpointChange_metric_congruence]
  calc
    endpointChange * (Aᵀ * endpointChangeInv) *
          (endpointChangeᵀ * hyperbolicMetricMatrix * endpointChange) +
        (endpointChangeᵀ * hyperbolicMetricMatrix * endpointChange) *
          (endpointChangeInv * A * endpointChange) =
    endpointChange * (Aᵀ * hyperbolicMetricMatrix +
        hyperbolicMetricMatrix * A) * endpointChange := by
          simp only [endpointChange_transpose]
          calc
            endpointChange * (Aᵀ * endpointChangeInv) *
                  (endpointChange * hyperbolicMetricMatrix * endpointChange) +
                (endpointChange * hyperbolicMetricMatrix * endpointChange) *
                  (endpointChangeInv * A * endpointChange) =
              endpointChange * (Aᵀ * (endpointChangeInv * endpointChange) *
                hyperbolicMetricMatrix * endpointChange) +
                endpointChange * hyperbolicMetricMatrix *
                  (endpointChange * endpointChangeInv) * A * endpointChange := by
                    noncomm_ring
            _ = endpointChange * (Aᵀ * hyperbolicMetricMatrix) * endpointChange +
                endpointChange * hyperbolicMetricMatrix * A * endpointChange := by
                  simp only [Matrix.mul_assoc, endpointChangeInv_mul,
                    endpointChange_mul_inv, Matrix.mul_one]
            _ = endpointChange * (Aᵀ * hyperbolicMetricMatrix +
                hyperbolicMetricMatrix * A) * endpointChange := by
                  noncomm_ring
    _ = 0 := by rw [hA]; simp

theorem diagonalToHyperbolic_preserves_constraint {A : HMatrix}
    (hA : Aᵀ * O55Form + O55Form * A = 0) :
    (diagonalToHyperbolic A)ᵀ * hyperbolicMetricMatrix +
      hyperbolicMetricMatrix * diagonalToHyperbolic A = 0 := by
  rw [diagonalToHyperbolic, Matrix.transpose_mul, Matrix.transpose_mul,
    endpointChangeInv_transpose, endpointChange_transpose,
    ← endpointChangeInv_metric_congruence]
  calc
    endpointChangeInv * (Aᵀ * endpointChange) *
          (endpointChangeInvᵀ * O55Form * endpointChangeInv) +
        (endpointChangeInvᵀ * O55Form * endpointChangeInv) *
          (endpointChange * A * endpointChangeInv) =
      endpointChangeInv * (Aᵀ * O55Form + O55Form * A) *
        endpointChangeInv := by
          simp only [endpointChangeInv_transpose]
          calc
            endpointChangeInv * (Aᵀ * endpointChange) *
                  (endpointChangeInv * O55Form * endpointChangeInv) +
                (endpointChangeInv * O55Form * endpointChangeInv) *
                  (endpointChange * A * endpointChangeInv) =
              endpointChangeInv * (Aᵀ * (endpointChange * endpointChangeInv) *
                O55Form * endpointChangeInv) +
                endpointChangeInv * O55Form *
                  (endpointChangeInv * endpointChange) * A * endpointChangeInv := by
                    noncomm_ring
            _ = endpointChangeInv * (Aᵀ * O55Form) * endpointChangeInv +
                endpointChangeInv * O55Form * A * endpointChangeInv := by
                  simp only [Matrix.mul_assoc, endpointChange_mul_inv,
                    endpointChangeInv_mul, Matrix.mul_one]
            _ = endpointChangeInv * (Aᵀ * O55Form +
                O55Form * A) * endpointChangeInv := by
                  noncomm_ring
    _ = 0 := by rw [hA]; simp

noncomputable def hyperbolicToDiagonalMap :
    HyperbolicOrthogonalLie →ₗ[ℝ] Orthogonal55 :=
  { toFun := fun A =>
      ⟨hyperbolicToDiagonal A.1,
        hyperbolicToDiagonal_preserves_constraint A.2⟩
    map_add' := by
      intro A B
      apply Subtype.ext
      simp [hyperbolicToDiagonal, mul_add, add_mul]
    map_smul' := by
      intro r A
      apply Subtype.ext
      simp [hyperbolicToDiagonal] }

noncomputable def diagonalToHyperbolicMap :
    Orthogonal55 →ₗ[ℝ] HyperbolicOrthogonalLie :=
  { toFun := fun A =>
      ⟨diagonalToHyperbolic A.1,
        diagonalToHyperbolic_preserves_constraint A.2⟩
    map_add' := by
      intro A B
      apply Subtype.ext
      simp [diagonalToHyperbolic, mul_add, add_mul]
    map_smul' := by
      intro r A
      apply Subtype.ext
      simp [diagonalToHyperbolic] }

noncomputable def hyperbolicDiagonalLinearEquiv :
    HyperbolicOrthogonalLie ≃ₗ[ℝ] Orthogonal55 :=
  { toFun := hyperbolicToDiagonalMap
    invFun := diagonalToHyperbolicMap
    left_inv := by
      intro A
      apply Subtype.ext
      change endpointChange *
          (endpointChangeInv * A.1 * endpointChange) * endpointChangeInv = A.1
      calc
        endpointChange * (endpointChangeInv * A.1 * endpointChange) *
              endpointChangeInv =
            (endpointChange * endpointChangeInv) * A.1 *
              (endpointChange * endpointChangeInv) := by
                noncomm_ring
        _ = A.1 := by
          simp only [endpointChange_mul_inv,
            Matrix.one_mul, Matrix.mul_one]
    right_inv := by
      intro A
      apply Subtype.ext
      change endpointChangeInv *
          (endpointChange * A.1 * endpointChangeInv) * endpointChange = A.1
      calc
        endpointChangeInv * (endpointChange * A.1 * endpointChangeInv) *
              endpointChange =
            (endpointChangeInv * endpointChange) * A.1 *
              (endpointChangeInv * endpointChange) := by
                noncomm_ring
        _ = A.1 := by
          simp only [endpointChangeInv_mul,
            Matrix.one_mul, Matrix.mul_one]
    map_add' := by intro A B; exact hyperbolicToDiagonalMap.map_add A B
    map_smul' := by intro r A; exact hyperbolicToDiagonalMap.map_smul r A }

theorem hyperbolicDiagonalLinearEquiv_apply (A : HyperbolicOrthogonalLie) :
    hyperbolicDiagonalLinearEquiv A =
      ⟨hyperbolicToDiagonal A.1,
        hyperbolicToDiagonal_preserves_constraint A.2⟩ :=
  -- This is the structure equation unfolding to the defining maps of the
  -- transport equivalence.
  by
    cases A with
    | mk A h =>
      rfl

theorem hyperbolicToDiagonal_bracket (A B : HyperbolicOrthogonalLie) :
    hyperbolicToDiagonalMap ⁅A, B⁆ =
      ⁅hyperbolicToDiagonalMap A, hyperbolicToDiagonalMap B⁆ := by
  apply Subtype.ext
  change endpointChangeInv * (A.1 * B.1 - B.1 * A.1) * endpointChange =
    (endpointChangeInv * A.1 * endpointChange) *
          (endpointChangeInv * B.1 * endpointChange) -
        (endpointChangeInv * B.1 * endpointChange) *
          (endpointChangeInv * A.1 * endpointChange)
  have hmul (X Y : HMatrix) :
      endpointChangeInv * (X * Y) * endpointChange =
        (endpointChangeInv * X * endpointChange) *
          (endpointChangeInv * Y * endpointChange) := by
    calc
      endpointChangeInv * (X * Y) * endpointChange =
          (endpointChangeInv * X) * (Y * endpointChange) := by
            simp only [Matrix.mul_assoc]
      _ = endpointChangeInv * X *
            (((endpointChange * endpointChangeInv) * Y) * endpointChange) := by
          rw [endpointChange_mul_inv]
          simp only [Matrix.one_mul, Matrix.mul_assoc]
      _ = (endpointChangeInv * X * endpointChange) *
            (endpointChangeInv * Y * endpointChange) := by
          simp only [Matrix.mul_assoc]
  calc
    endpointChangeInv * (A.1 * B.1 - B.1 * A.1) * endpointChange =
        endpointChangeInv * (A.1 * B.1) * endpointChange -
          endpointChangeInv * (B.1 * A.1) * endpointChange := by
            rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = (endpointChangeInv * A.1 * endpointChange) *
          (endpointChangeInv * B.1 * endpointChange) -
        (endpointChangeInv * B.1 * endpointChange) *
          (endpointChangeInv * A.1 * endpointChange) := by
            rw [hmul, hmul]

theorem diagonalToHyperbolic_bracket (A B : Orthogonal55) :
    diagonalToHyperbolicMap ⁅A, B⁆ =
      ⁅diagonalToHyperbolicMap A, diagonalToHyperbolicMap B⁆ := by
  apply Subtype.ext
  change endpointChange * (A.1 * B.1 - B.1 * A.1) * endpointChangeInv =
    (endpointChange * A.1 * endpointChangeInv) *
          (endpointChange * B.1 * endpointChangeInv) -
        (endpointChange * B.1 * endpointChangeInv) *
          (endpointChange * A.1 * endpointChangeInv)
  have hmul (X Y : HMatrix) :
      endpointChange * (X * Y) * endpointChangeInv =
        (endpointChange * X * endpointChangeInv) *
          (endpointChange * Y * endpointChangeInv) := by
    calc
      endpointChange * (X * Y) * endpointChangeInv =
          (endpointChange * X) * (Y * endpointChangeInv) := by
            simp only [Matrix.mul_assoc]
      _ = endpointChange * X *
            (((endpointChangeInv * endpointChange) * Y) * endpointChangeInv) := by
          rw [endpointChangeInv_mul]
          simp only [Matrix.one_mul, Matrix.mul_assoc]
      _ = (endpointChange * X * endpointChangeInv) *
            (endpointChange * Y * endpointChangeInv) := by
          simp only [Matrix.mul_assoc]
  calc
    endpointChange * (A.1 * B.1 - B.1 * A.1) * endpointChangeInv =
        endpointChange * (A.1 * B.1) * endpointChangeInv -
          endpointChange * (B.1 * A.1) * endpointChangeInv := by
            rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = (endpointChange * A.1 * endpointChangeInv) *
          (endpointChange * B.1 * endpointChangeInv) -
        (endpointChange * B.1 * endpointChangeInv) *
          (endpointChange * A.1 * endpointChangeInv) := by
            rw [hmul, hmul]

noncomputable def hyperbolicDiagonalLieEquiv :
    HyperbolicOrthogonalLie ≃ₗ⁅ℝ⁆ Orthogonal55 := by
  refine LieEquiv.mk
    (LieHom.mk hyperbolicToDiagonalMap (by
      intro A B
      exact hyperbolicToDiagonal_bracket A B))
    diagonalToHyperbolicMap ?_ ?_
  · intro A
    apply Subtype.ext
    change endpointChange *
        (endpointChangeInv * A.1 * endpointChange) * endpointChangeInv = A.1
    calc
      endpointChange * (endpointChangeInv * A.1 * endpointChange) *
            endpointChangeInv =
          (endpointChange * endpointChangeInv) * A.1 *
            (endpointChange * endpointChangeInv) := by
              noncomm_ring
      _ = A.1 := by
        simp only [endpointChange_mul_inv,
          Matrix.one_mul, Matrix.mul_one]
  · intro A
    apply Subtype.ext
    change endpointChangeInv *
        (endpointChange * A.1 * endpointChangeInv) * endpointChange = A.1
    calc
      endpointChangeInv * (endpointChange * A.1 * endpointChangeInv) *
            endpointChange =
          (endpointChangeInv * endpointChange) * A.1 *
            (endpointChangeInv * endpointChange) := by
              noncomm_ring
      _ = A.1 := by
        simp only [endpointChangeInv_mul,
          Matrix.one_mul, Matrix.mul_one]

theorem hyperbolicDiagonalLieEquiv_apply
    (A : HyperbolicOrthogonalLie) :
    hyperbolicDiagonalLieEquiv A =
      ⟨hyperbolicToDiagonal A.1,
        hyperbolicToDiagonal_preserves_constraint A.2⟩ := by
  unfold hyperbolicDiagonalLieEquiv
  apply Subtype.ext
  rfl

end InfoGeometry.Canonical.HyperbolicDiagonalO55
