import proofs.TKK55Complexification
import proofs.D5IsotropicDiagonalLieEquiv
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Complex diagonal matrices as the scalar extension of real `so(5,5)` -/

noncomputable section
set_option maxHeartbeats 1000000
namespace D5DiagonalComplexification

open scoped TensorProduct
open SplitOctonionTKK55 SO55HyperbolicDiagonalLieEquiv TKK55Complexification
open D5ComplexMatrixRootSpaces D5IsotropicDiagonalLieEquiv

abbrev CM10Fin := Matrix (Fin 10) (Fin 10) ℂ

def complexEta55 : CM10Fin := fun i j => (eta55 i j : ℂ)

def complexDiagonalSO55Submodule : Submodule ℂ CM10Fin where
  carrier := {A | A.transpose * complexEta55 + complexEta55 * A = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change (A + B).transpose * complexEta55 + complexEta55 * (A + B) = 0
    simp only [Matrix.transpose_add, add_mul, mul_add]
    calc
      (A.transpose * complexEta55 + B.transpose * complexEta55) +
          (complexEta55 * A + complexEta55 * B) =
        (A.transpose * complexEta55 + complexEta55 * A) +
          (B.transpose * complexEta55 + complexEta55 * B) := by abel
      _ = 0 := by rw [hA, hB]; simp
  smul_mem' := by
    intro z A hA
    change (z • A).transpose * complexEta55 + complexEta55 * (z • A) = 0
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add, hA, smul_zero]

def complexDiagonalSO55 : LieSubalgebra ℂ CM10Fin :=
  LieSubalgebra.mk complexDiagonalSO55Submodule (by
    intro A B hA hB
    change (A * B - B * A).transpose * complexEta55 +
      complexEta55 * (A * B - B * A) = 0
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
    have hAt : A.transpose * complexEta55 = -(complexEta55 * A) :=
      eq_neg_of_add_eq_zero_left hA
    have hBt : B.transpose * complexEta55 = -(complexEta55 * B) :=
      eq_neg_of_add_eq_zero_left hB
    simp only [mul_sub, sub_mul]
    rw [Matrix.mul_assoc B.transpose A.transpose complexEta55,
      Matrix.mul_assoc A.transpose B.transpose complexEta55, hAt, hBt]
    simp only [mul_neg]
    rw [← Matrix.mul_assoc B.transpose complexEta55 A,
      ← Matrix.mul_assoc A.transpose complexEta55 B, hBt, hAt]
    noncomm_ring)

def embedRealMatrix (A : M10) : CM10Fin := fun i j => (A i j : ℂ)
def realPartMatrix (A : CM10Fin) : M10 := fun i j => (A i j).re
def imagPartMatrix (A : CM10Fin) : M10 := fun i j => (A i j).im

@[simp] theorem embedRealMatrix_add (A B : M10) :
    embedRealMatrix (A + B) = embedRealMatrix A + embedRealMatrix B := by
  ext i j
  simp [embedRealMatrix]

@[simp] theorem embedRealMatrix_sub (A B : M10) :
    embedRealMatrix (A - B) = embedRealMatrix A - embedRealMatrix B := by
  ext i j
  simp [embedRealMatrix]

@[simp] theorem embedRealMatrix_smul (r : ℝ) (A : M10) :
    embedRealMatrix (r • A) = (r : ℂ) • embedRealMatrix A := by
  ext i j
  simp [embedRealMatrix]

@[simp] theorem embedRealMatrix_transpose (A : M10) :
    embedRealMatrix A.transpose = (embedRealMatrix A).transpose := rfl

@[simp] theorem embedRealMatrix_mul (A B : M10) :
    embedRealMatrix (A * B) = embedRealMatrix A * embedRealMatrix B := by
  ext i j
  simp [embedRealMatrix, Matrix.mul_apply, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul]

@[simp] theorem embedRealMatrix_eta : embedRealMatrix eta55 = complexEta55 := rfl

def embedRealDiagonal (A : diagonalSO55) : complexDiagonalSO55 := by
  refine ⟨embedRealMatrix A, ?_⟩
  change embedRealMatrix A.1.transpose * embedRealMatrix eta55 +
    embedRealMatrix eta55 * embedRealMatrix A.1 = 0
  rw [← embedRealMatrix_mul, ← embedRealMatrix_mul,
    ← embedRealMatrix_add, A.property]
  rfl

theorem realPart_add (A B : CM10Fin) :
    realPartMatrix (A + B) = realPartMatrix A + realPartMatrix B := by
  ext i j
  simp [realPartMatrix]

theorem imagPart_add (A B : CM10Fin) :
    imagPartMatrix (A + B) = imagPartMatrix A + imagPartMatrix B := by
  ext i j
  simp [imagPartMatrix]

theorem realPart_transpose (A : CM10Fin) :
    realPartMatrix A.transpose = (realPartMatrix A).transpose := rfl

theorem imagPart_transpose (A : CM10Fin) :
    imagPartMatrix A.transpose = (imagPartMatrix A).transpose := rfl

theorem realPart_mul_real_right (A : CM10Fin) (B : M10) :
    realPartMatrix (A * embedRealMatrix B) = realPartMatrix A * B := by
  ext i j
  simp [realPartMatrix, embedRealMatrix, Matrix.mul_apply, Complex.mul_re]

theorem realPart_mul_real_left (A : M10) (B : CM10Fin) :
    realPartMatrix (embedRealMatrix A * B) = A * realPartMatrix B := by
  ext i j
  simp [realPartMatrix, embedRealMatrix, Matrix.mul_apply, Complex.mul_re]

theorem imagPart_mul_real_right (A : CM10Fin) (B : M10) :
    imagPartMatrix (A * embedRealMatrix B) = imagPartMatrix A * B := by
  ext i j
  simp [imagPartMatrix, embedRealMatrix, Matrix.mul_apply, Complex.mul_im]

theorem imagPart_mul_real_left (A : M10) (B : CM10Fin) :
    imagPartMatrix (embedRealMatrix A * B) = A * imagPartMatrix B := by
  ext i j
  simp [imagPartMatrix, embedRealMatrix, Matrix.mul_apply, Complex.mul_im]

theorem realPart_zero : realPartMatrix 0 = 0 := by
  ext i j
  simp [realPartMatrix]
theorem imagPart_zero : imagPartMatrix 0 = 0 := by
  ext i j
  simp [imagPartMatrix]

def realPartDiagonal (A : complexDiagonalSO55) : diagonalSO55 := by
  refine ⟨realPartMatrix A, ?_⟩
  have h := congrArg realPartMatrix A.property
  simpa [complexEta55, ← embedRealMatrix_eta, realPart_add,
    realPart_transpose, realPart_mul_real_right, realPart_mul_real_left,
    realPart_zero] using h

def imagPartDiagonal (A : complexDiagonalSO55) : diagonalSO55 := by
  refine ⟨imagPartMatrix A, ?_⟩
  have h := congrArg imagPartMatrix A.property
  simpa [complexEta55, ← embedRealMatrix_eta, imagPart_add,
    imagPart_transpose, imagPart_mul_real_right, imagPart_mul_real_left,
    imagPart_zero] using h

def scalarEmbed (z : ℂ) : diagonalSO55 →ₗ[ℝ] complexDiagonalSO55 where
  toFun A := z • embedRealDiagonal A
  map_add' A B := by apply Subtype.ext; simp [embedRealDiagonal, smul_add]
  map_smul' r A := by
    apply Subtype.ext
    ext i j
    simp [embedRealDiagonal, embedRealMatrix]
    ring

def scalarEmbedLinear : ℂ →ₗ[ℂ] diagonalSO55 →ₗ[ℝ] complexDiagonalSO55 where
  toFun := scalarEmbed
  map_add' z w := by ext A; simp [scalarEmbed, add_smul]
  map_smul' z w := by ext A; simp [scalarEmbed, mul_smul]

def complexificationToDiagonal : ComplexDiagonalSO55 →ₗ[ℂ] complexDiagonalSO55 :=
  TensorProduct.AlgebraTensorModule.lift scalarEmbedLinear

@[simp] theorem complexificationToDiagonal_tmul (z : ℂ) (A : diagonalSO55) :
    complexificationToDiagonal (z ⊗ₜ[ℝ] A) = z • embedRealDiagonal A := rfl

def diagonalToComplexification (A : complexDiagonalSO55) : ComplexDiagonalSO55 :=
  (1 : ℂ) ⊗ₜ[ℝ] realPartDiagonal A + Complex.I ⊗ₜ[ℝ] imagPartDiagonal A

@[simp] theorem realPartDiagonal_zero : realPartDiagonal 0 = 0 := by
  apply Subtype.ext
  ext i j
  simp [realPartDiagonal, realPartMatrix]

@[simp] theorem imagPartDiagonal_zero : imagPartDiagonal 0 = 0 := by
  apply Subtype.ext
  ext i j
  simp [imagPartDiagonal, imagPartMatrix]

@[simp] theorem realPartDiagonal_add (A B : complexDiagonalSO55) :
    realPartDiagonal (A + B) = realPartDiagonal A + realPartDiagonal B := by
  apply Subtype.ext
  exact realPart_add A B

@[simp] theorem imagPartDiagonal_add (A B : complexDiagonalSO55) :
    imagPartDiagonal (A + B) = imagPartDiagonal A + imagPartDiagonal B := by
  apply Subtype.ext
  exact imagPart_add A B

@[simp] theorem realPart_smul_embed (z : ℂ) (A : diagonalSO55) :
    realPartDiagonal (z • embedRealDiagonal A) = z.re • A := by
  apply Subtype.ext
  ext i j
  simp [realPartDiagonal, realPartMatrix, embedRealDiagonal, embedRealMatrix,
    Complex.mul_re]

@[simp] theorem imagPart_smul_embed (z : ℂ) (A : diagonalSO55) :
    imagPartDiagonal (z • embedRealDiagonal A) = z.im • A := by
  apply Subtype.ext
  ext i j
  simp [imagPartDiagonal, imagPartMatrix, embedRealDiagonal, embedRealMatrix,
    Complex.mul_im]

theorem complexification_rightInverse (A : complexDiagonalSO55) :
    complexificationToDiagonal (diagonalToComplexification A) = A := by
  apply Subtype.ext
  ext i j
  apply Complex.ext <;>
    simp [diagonalToComplexification, realPartDiagonal, imagPartDiagonal,
      realPartMatrix, imagPartMatrix, embedRealDiagonal, embedRealMatrix]

theorem complexification_leftInverse (x : ComplexDiagonalSO55) :
    diagonalToComplexification (complexificationToDiagonal x) = x := by
  refine x.induction_on ?_ ?_ ?_
  · simp [diagonalToComplexification]
  · intro z A
    change diagonalToComplexification (z • embedRealDiagonal A) = z ⊗ₜ[ℝ] A
    simp only [diagonalToComplexification, realPart_smul_embed,
      imagPart_smul_embed]
    rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]
    change ((z.re : ℂ) * 1) ⊗ₜ[ℝ] A +
      ((z.im : ℂ) * Complex.I) ⊗ₜ[ℝ] A = z ⊗ₜ[ℝ] A
    rw [← TensorProduct.add_tmul]
    simp only [mul_one, Complex.re_add_im]
  · intro x y hx hy
    rw [map_add]
    change diagonalToComplexification
      (complexificationToDiagonal x + complexificationToDiagonal y) = x + y
    rw [show diagonalToComplexification
      (complexificationToDiagonal x + complexificationToDiagonal y) =
        diagonalToComplexification (complexificationToDiagonal x) +
          diagonalToComplexification (complexificationToDiagonal y) by
      simp [diagonalToComplexification, TensorProduct.tmul_add]
      abel]
    rw [hx, hy]

def diagonalComplexificationLinearEquiv :
    ComplexDiagonalSO55 ≃ₗ[ℂ] complexDiagonalSO55 where
  toLinearMap := complexificationToDiagonal
  invFun := diagonalToComplexification
  left_inv := complexification_leftInverse
  right_inv := complexification_rightInverse

theorem complexificationToDiagonal_lie
    (x y : ComplexDiagonalSO55) :
    complexificationToDiagonal ⁅x, y⁆ =
      ⁅complexificationToDiagonal x, complexificationToDiagonal y⁆ := by
  refine x.induction_on ?_ ?_ ?_
  · simp
  · intro z A
    refine y.induction_on ?_ ?_ ?_
    · have hz : ⁅z ⊗ₜ[ℝ] A, (0 : ComplexDiagonalSO55)⁆ = 0 :=
        @lie_zero ComplexDiagonalSO55 ComplexDiagonalSO55
          (LieAlgebra.ExtendScalars.instLieRing ℝ ℂ diagonalSO55)
          inferInstance
          (LieAlgebra.ExtendScalars.instLieRingModule ℝ ℂ diagonalSO55 diagonalSO55)
          (z ⊗ₜ[ℝ] A)
      calc
        complexificationToDiagonal ⁅z ⊗ₜ[ℝ] A, 0⁆ =
            complexificationToDiagonal 0 := by rw [hz]
        _ = 0 := map_zero _
        _ = ⁅complexificationToDiagonal (z ⊗ₜ[ℝ] A),
            complexificationToDiagonal 0⁆ := by rw [map_zero, lie_zero]
    · intro w B
      apply Subtype.ext
      change (z * w) • embedRealMatrix (A.1 * B.1 - B.1 * A.1) =
        (z • embedRealMatrix A.1) * (w • embedRealMatrix B.1) -
          (w • embedRealMatrix B.1) * (z • embedRealMatrix A.1)
      rw [embedRealMatrix_sub, embedRealMatrix_mul, embedRealMatrix_mul]
      simp
      module
    · intro u v hu hv
      have hadd : ⁅z ⊗ₜ[ℝ] A, u + v⁆ =
          ⁅z ⊗ₜ[ℝ] A, u⁆ + ⁅z ⊗ₜ[ℝ] A, v⁆ :=
        @lie_add ComplexDiagonalSO55 ComplexDiagonalSO55
          (LieAlgebra.ExtendScalars.instLieRing ℝ ℂ diagonalSO55)
          inferInstance
          (LieAlgebra.ExtendScalars.instLieRingModule ℝ ℂ diagonalSO55 diagonalSO55)
          (z ⊗ₜ[ℝ] A) u v
      calc
        complexificationToDiagonal ⁅z ⊗ₜ[ℝ] A, u + v⁆ =
            complexificationToDiagonal
              (⁅z ⊗ₜ[ℝ] A, u⁆ + ⁅z ⊗ₜ[ℝ] A, v⁆) := by rw [hadd]
        _ = complexificationToDiagonal ⁅z ⊗ₜ[ℝ] A, u⁆ +
            complexificationToDiagonal ⁅z ⊗ₜ[ℝ] A, v⁆ := map_add _ _ _
        _ = ⁅complexificationToDiagonal (z ⊗ₜ[ℝ] A),
              complexificationToDiagonal u⁆ +
            ⁅complexificationToDiagonal (z ⊗ₜ[ℝ] A),
              complexificationToDiagonal v⁆ := by rw [hu, hv]
        _ = ⁅complexificationToDiagonal (z ⊗ₜ[ℝ] A),
              complexificationToDiagonal (u + v)⁆ := by rw [map_add, lie_add]
  · intro u v hu hv
    have hadd : ⁅u + v, y⁆ = ⁅u, y⁆ + ⁅v, y⁆ := add_lie _ _ _
    calc
      complexificationToDiagonal ⁅u + v, y⁆ =
          complexificationToDiagonal (⁅u, y⁆ + ⁅v, y⁆) := by rw [hadd]
      _ = complexificationToDiagonal ⁅u, y⁆ +
          complexificationToDiagonal ⁅v, y⁆ := map_add _ _ _
      _ = ⁅complexificationToDiagonal u, complexificationToDiagonal y⁆ +
          ⁅complexificationToDiagonal v, complexificationToDiagonal y⁆ := by
            rw [hu, hv]
      _ = ⁅complexificationToDiagonal (u + v),
          complexificationToDiagonal y⁆ := by rw [map_add, add_lie]

def diagonalComplexificationLieEquiv :
    ComplexDiagonalSO55 ≃ₗ⁅ℂ⁆ complexDiagonalSO55 :=
  LieEquiv.ofBijective
    { toLinearMap := complexificationToDiagonal
      map_lie' := fun {x y} => complexificationToDiagonal_lie x y }
    diagonalComplexificationLinearEquiv.bijective

def isoFin10 : IsoIndex ≃ Fin 10 := finSumFinEquiv

private def reindexAlg : CM10 ≃ₐ[ℂ] CM10Fin :=
  Matrix.reindexAlgEquiv ℂ ℂ isoFin10

theorem unreindex_complexEta : reindexAlg.symm complexEta55 = diagonalMetric := by
  have hleft (i : Fin 5) :
      ((finSumFinEquiv : Fin 5 ⊕ Fin 5 ≃ Fin 10) (.inl i)).val < 5 := by
    change i.val < 5
    exact i.isLt
  have hright (i : Fin 5) :
      ¬((finSumFinEquiv : Fin 5 ⊕ Fin 5 ≃ Fin 10) (.inr i)).val < 5 := by
    change ¬(5 + i.val < 5)
    omega
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [reindexAlg, isoFin10, diagonalMetric, complexEta55, eta55,
      Matrix.reindexAlgEquiv, Matrix.reindex, Fin.ext_iff,
      hleft, hright]
  all_goals split_ifs <;> norm_num

theorem reindex_diagonalMetric : reindexAlg diagonalMetric = complexEta55 := by
  apply reindexAlg.symm.injective
  rw [reindexAlg.symm_apply_apply, unreindex_complexEta]

theorem reindex_transpose (A : CM10) :
    reindexAlg A.transpose = (reindexAlg A).transpose := by
  exact Matrix.transpose_reindex isoFin10 isoFin10 A

def reindexDiagonal (A : diagonalSO10) : complexDiagonalSO55 := by
  refine ⟨reindexAlg A, ?_⟩
  change (reindexAlg A).transpose * complexEta55 +
    complexEta55 * reindexAlg A = 0
  rw [← reindex_diagonalMetric, ← reindex_transpose,
    ← map_mul, ← map_mul, ← map_add, A.property, map_zero]

def unreindexDiagonal (A : complexDiagonalSO55) : diagonalSO10 := by
  refine ⟨reindexAlg.symm A, ?_⟩
  apply reindexAlg.injective
  change reindexAlg ((reindexAlg.symm A).transpose * diagonalMetric +
    diagonalMetric * reindexAlg.symm A) = 0
  rw [map_add, map_mul, map_mul, reindex_transpose,
    reindex_diagonalMetric, reindexAlg.apply_symm_apply]
  exact A.property

def reindexDiagonalLinear : diagonalSO10 →ₗ[ℂ] complexDiagonalSO55 where
  toFun := reindexDiagonal
  map_add' A B := by
    apply Subtype.ext
    change reindexAlg (A.1 + B.1) = reindexAlg A.1 + reindexAlg B.1
    exact map_add reindexAlg A.1 B.1
  map_smul' z A := by
    apply Subtype.ext
    change reindexAlg (z • A.1) = z • reindexAlg A.1
    exact map_smul reindexAlg z A.1

theorem reindexDiagonal_lie (A B : diagonalSO10) :
    reindexDiagonalLinear ⁅A, B⁆ =
      ⁅reindexDiagonalLinear A, reindexDiagonalLinear B⁆ := by
  apply Subtype.ext
  change reindexAlg (A.1 * B.1 - B.1 * A.1) =
    reindexAlg A.1 * reindexAlg B.1 - reindexAlg B.1 * reindexAlg A.1
  rw [map_sub, map_mul, map_mul]

def reindexDiagonalLieEquiv : diagonalSO10 ≃ₗ⁅ℂ⁆ complexDiagonalSO55 :=
  LieEquiv.ofBijective
    { toLinearMap := reindexDiagonalLinear
      map_lie' := fun {x y} => reindexDiagonal_lie x y }
    ⟨fun _ _ h => Subtype.ext (reindexAlg.injective (congrArg Subtype.val h)),
      fun A => ⟨unreindexDiagonal A, by
        apply Subtype.ext
        exact reindexAlg.apply_symm_apply A.1⟩⟩

end D5DiagonalComplexification
end noncomputable section
