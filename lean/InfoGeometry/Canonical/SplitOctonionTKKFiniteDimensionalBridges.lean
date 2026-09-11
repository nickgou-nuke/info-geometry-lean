import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.TKKClosure

namespace InfoGeometry.Canonical.SplitOctonionTKKFiniteDimensionalBridges

open LieAlgebra

abbrev Skew4 := skewAdjointMatricesSubmodule (1 : Matrix (Fin 4) (Fin 4) ℝ)
abbrev So44 := LieAlgebra.Orthogonal.so' (Fin 4) (Fin 4) ℝ
abbrev StructureAlgebraCarrier := So44 × ℝ

def skewMatrix (x : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, x 0, x 1, x 2;
     -x 0, 0, x 3, x 4;
     -x 1, -x 3, 0, x 5;
     -x 2, -x 4, -x 5, 0]

theorem skewMatrix_skew (x : Fin 6 → ℝ) :
    Matrix.transpose (skewMatrix x) = -skewMatrix x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMatrix, Matrix.transpose_apply] <;> ring

def skewMatrixLinear : (Fin 6 → ℝ) →ₗ[ℝ] Skew4 where
  toFun x := ⟨skewMatrix x, by
    simpa [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] using skewMatrix_skew x⟩
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrix] <;> ring
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrix] <;> ring

def skewCoords : Skew4 →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun A := ![A.1 0 1, A.1 0 2, A.1 0 3, A.1 1 2, A.1 1 3, A.1 2 3]
  map_add' A B := by funext i; fin_cases i <;> rfl
  map_smul' c A := by funext i; fin_cases i <;> rfl

def skewEquiv : Skew4 ≃ₗ[ℝ] (Fin 6 → ℝ) where
  toFun := skewCoords
  invFun := skewMatrixLinear
  left_inv A := by
    have hA : Matrix.transpose A.1 = -A.1 := by
      have h := A.2
      rw [mem_skewAdjointMatricesSubmodule] at h
      change Matrix.transpose A.1 * (1 : Matrix (Fin 4) (Fin 4) ℝ) =
        (1 : Matrix (Fin 4) (Fin 4) ℝ) * (-A.1) at h
      simpa only [Matrix.mul_one, Matrix.one_mul] using h
    apply Subtype.ext
    ext i j
    have h := congrArg
      (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hA
    fin_cases i <;> fin_cases j <;>
      simp [skewCoords, skewMatrixLinear, skewMatrix, Matrix.transpose_apply] at h ⊢ <;>
      linarith
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' := skewCoords.map_add
  map_smul' := skewCoords.map_smul

theorem skew4_finrank : Module.finrank ℝ Skew4 = 6 := by
  rw [skewEquiv.finrank_eq]
  simp

abbrev Block44 := Skew4 × Matrix (Fin 4) (Fin 4) ℝ × Skew4

def D44 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 4) (Fin 4) ℝ

def blockMatrix44 (x : Block44) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ :=
  Matrix.fromBlocks x.1.1 x.2.1 (Matrix.transpose x.2.1) x.2.2.1

def blockToSo44 : Block44 →ₗ[ℝ] So44 where
  toFun x := ⟨blockMatrix44 x, by
    have ht := x.1.2
    rw [mem_skewAdjointMatricesSubmodule] at ht
    have hb := x.2.2.2
    rw [mem_skewAdjointMatricesSubmodule] at hb
    change blockMatrix44 x ∈ skewAdjointMatricesSubmodule D44
    rw [mem_skewAdjointMatricesSubmodule]
    change _ = _
    ext r c
    rcases r with r | r <;> rcases c with c | c <;>
      simp [blockMatrix44, D44, Matrix.mul_apply, Fintype.sum_sum_type,
        LieAlgebra.Orthogonal.indefiniteDiagonal, Matrix.diagonal_apply,
        Finset.sum_ite_eq'] <;> ring
    all_goals
      first
      | simpa [Matrix.transpose_apply] using congrArg
          (fun M : Matrix (Fin 4) (Fin 4) ℝ => M r c) ht
      | have hh := congrArg
          (fun M : Matrix (Fin 4) (Fin 4) ℝ => M r c) hb
        simp [Matrix.transpose_apply] at hh ⊢
        linarith⟩
  map_add' x y := by
    ext r c
    rcases r with r | r <;> rcases c with c | c <;> rfl
  map_smul' a x := by
    ext r c
    rcases r with r | r <;> rcases c with c | c <;> rfl

def topBlock (X : So44) : Skew4 :=
  ⟨fun i j => X.1 (Sum.inl i) (Sum.inl j), by
    have h := X.2
    change X.1 ∈ skewAdjointMatricesSubmodule D44 at h
    rw [mem_skewAdjointMatricesSubmodule] at h
    rw [mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_one, Matrix.one_mul]
    ext i j
    have hij := congr_fun (congr_fun h (Sum.inl i)) (Sum.inl j)
    simpa [D44, Matrix.mul_apply, LieAlgebra.Orthogonal.indefiniteDiagonal,
      Matrix.diagonal_apply, Finset.sum_ite_eq'] using hij⟩

def middleBlock (X : So44) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => X.1 (Sum.inl i) (Sum.inr j)

def bottomBlock (X : So44) : Skew4 :=
  ⟨fun i j => X.1 (Sum.inr i) (Sum.inr j), by
    have h := X.2
    change X.1 ∈ skewAdjointMatricesSubmodule D44 at h
    rw [mem_skewAdjointMatricesSubmodule] at h
    rw [mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_one, Matrix.one_mul]
    ext i j
    have hij := congr_fun (congr_fun h (Sum.inr i)) (Sum.inr j)
    simp [D44, Matrix.mul_apply, LieAlgebra.Orthogonal.indefiniteDiagonal,
      Matrix.diagonal_apply, Finset.sum_ite_eq'] at hij ⊢
    linarith⟩

def blockFromSo44 : So44 →ₗ[ℝ] Block44 where
  toFun X := (topBlock X, middleBlock X, bottomBlock X)
  map_add' X Y := by ext <;> rfl
  map_smul' a X := by ext <;> rfl

def blockEquiv : So44 ≃ₗ[ℝ] Block44 where
  toFun := blockFromSo44
  invFun := blockToSo44
  left_inv X := by
    have h := X.2
    change X.1 ∈ skewAdjointMatricesSubmodule D44 at h
    rw [mem_skewAdjointMatricesSubmodule] at h
    apply Subtype.ext
    ext r c
    rcases r with r | r <;> rcases c with c | c <;>
      simp [blockToSo44, blockFromSo44, blockMatrix44, topBlock, middleBlock,
        bottomBlock,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] at *
    all_goals
      first
      | rfl
      | have hrc := congr_fun (congr_fun h (Sum.inr r)) (Sum.inl c)
        simpa [D44, Matrix.mul_apply, LieAlgebra.Orthogonal.indefiniteDiagonal,
          Matrix.diagonal_apply, Finset.sum_ite_eq'] using hrc
  right_inv x := by
    ext r c
    rcases r with r | r <;> rcases c with c | c <;>
      simp [blockToSo44, blockFromSo44, blockMatrix44, topBlock, middleBlock,
        bottomBlock,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;> rfl
    all_goals
      first
      | change x.2.1 r c = x.2.1 r c
        rfl
      | change (x.2.2.1 : Matrix (Fin 4) (Fin 4) ℝ) r c = x.2.2.1 r c
        rfl
  map_add' := blockFromSo44.map_add
  map_smul' := blockFromSo44.map_smul

theorem so44_finrank : Module.finrank ℝ So44 = 28 := by
  rw [blockEquiv.finrank_eq, Module.finrank_prod, Module.finrank_prod,
    skew4_finrank]
  simp [Module.finrank_matrix]

theorem structure_algebra_finrank :
    Module.finrank ℝ StructureAlgebraCarrier = 29 := by
  rw [Module.finrank_prod, so44_finrank, Module.finrank_self]

def structureAlgebraFinrank (hSo44 : Module.finrank ℝ So44 = 28) :
    Module.finrank ℝ StructureAlgebraCarrier = 29 := by
  rw [Module.finrank_prod, hSo44, Module.finrank_self]

theorem structure_algebra_finrank_of (hSo44 : Module.finrank ℝ So44 = 28) :
    Module.finrank ℝ StructureAlgebraCarrier = 29 :=
  structureAlgebraFinrank hSo44

def structureAlgebraBlockEquiv :
    StructureAlgebraCarrier ≃ₗ[ℝ] Block44 × ℝ :=
  LinearEquiv.prodCongr blockEquiv (LinearEquiv.refl ℝ ℝ)

theorem structure_algebra_block_finrank :
    Module.finrank ℝ (Block44 × ℝ) = 29 := by
  calc
    Module.finrank ℝ (Block44 × ℝ) =
        Module.finrank ℝ StructureAlgebraCarrier :=
      structureAlgebraBlockEquiv.finrank_eq.symm
    _ = 29 := structure_algebra_finrank

abbrev TKKBlockCarrier :=
  (Fin 10 → ℝ) × (Matrix (Fin 5) (Fin 5) ℝ) × (Fin 10 → ℝ)

theorem tkk_block_carrier_finrank :
    Module.finrank ℝ TKKBlockCarrier = 45 := by
  rw [Module.finrank_prod, Module.finrank_prod]
  simp [Module.finrank_matrix]

def blockFinrankEquiv {L : Type*} [AddCommGroup L] [Module ℝ L]
    (e : TKKBlockCarrier ≃ₗ[ℝ] L)
    [Module.Finite ℝ L] :
    Module.finrank ℝ L = 45 := by
  calc
    Module.finrank ℝ L = Module.finrank ℝ TKKBlockCarrier :=
      e.finrank_eq.symm
    _ = 45 := tkk_block_carrier_finrank

theorem block_finrank_of_equiv
    {L : Type*} [AddCommGroup L] [Module ℝ L] [Module.Finite ℝ L]
    (e : TKKBlockCarrier ≃ₗ[ℝ] L) :
    Module.finrank ℝ L = 45 :=
  blockFinrankEquiv e

abbrev Skew5 := skewAdjointMatricesSubmodule (1 : Matrix (Fin 5) (Fin 5) ℝ)
abbrev So55 := LieAlgebra.Orthogonal.so' (Fin 5) (Fin 5) ℝ
abbrev Block55 := Skew5 × Matrix (Fin 5) (Fin 5) ℝ × Skew5

def skewMatrix5 (x : Fin 10 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, x 0, x 1, x 2, x 3;
     -x 0, 0, x 4, x 5, x 6;
     -x 1, -x 4, 0, x 7, x 8;
     -x 2, -x 5, -x 7, 0, x 9;
     -x 3, -x 6, -x 8, -x 9, 0]

theorem skewMatrix5_skew (x : Fin 10 → ℝ) :
    Matrix.transpose (skewMatrix5 x) = -skewMatrix5 x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewMatrix5, Matrix.transpose_apply] <;> ring

def skewMatrix5Linear : (Fin 10 → ℝ) →ₗ[ℝ] Skew5 where
  toFun x := ⟨skewMatrix5 x, by
    simpa [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] using skewMatrix5_skew x⟩
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrix5] <;> ring
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skewMatrix5] <;> ring

def skewCoords5 : Skew5 →ₗ[ℝ] (Fin 10 → ℝ) where
  toFun A := ![A.1 0 1, A.1 0 2, A.1 0 3, A.1 0 4,
    A.1 1 2, A.1 1 3, A.1 1 4, A.1 2 3, A.1 2 4, A.1 3 4]
  map_add' A B := by funext i; fin_cases i <;> rfl
  map_smul' c A := by funext i; fin_cases i <;> rfl

def skewEquiv5 : Skew5 ≃ₗ[ℝ] (Fin 10 → ℝ) where
  toFun := skewCoords5
  invFun := skewMatrix5Linear
  left_inv A := by
    have hA : Matrix.transpose A.1 = -A.1 := by
      have h := A.2
      rw [mem_skewAdjointMatricesSubmodule] at h
      change Matrix.transpose A.1 * (1 : Matrix (Fin 5) (Fin 5) ℝ) =
        (1 : Matrix (Fin 5) (Fin 5) ℝ) * (-A.1) at h
      simpa only [Matrix.mul_one, Matrix.one_mul] using h
    apply Subtype.ext
    ext i j
    have h := congrArg
      (fun M : Matrix (Fin 5) (Fin 5) ℝ => M i j) hA
    fin_cases i <;> fin_cases j <;>
      simp [skewCoords5, skewMatrix5Linear, skewMatrix5, Matrix.transpose_apply] at h ⊢ <;>
      linarith
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' := skewCoords5.map_add
  map_smul' := skewCoords5.map_smul

def D55 : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ :=
  LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 5) (Fin 5) ℝ

def blockMatrix55 (x : Block55) :
    Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) ℝ :=
  Matrix.fromBlocks x.1.1 x.2.1 (Matrix.transpose x.2.1) x.2.2.1

def blockToSo55 : Block55 →ₗ[ℝ] So55 where
  toFun x := ⟨blockMatrix55 x, by
    have ht := x.1.2
    rw [mem_skewAdjointMatricesSubmodule] at ht
    have hb := x.2.2.2
    rw [mem_skewAdjointMatricesSubmodule] at hb
    change blockMatrix55 x ∈ skewAdjointMatricesSubmodule D55
    rw [mem_skewAdjointMatricesSubmodule]
    change _ = _
    ext r c
    rcases r with r | r <;> rcases c with c | c <;>
      simp [blockMatrix55, D55, Matrix.mul_apply, Fintype.sum_sum_type,
        LieAlgebra.Orthogonal.indefiniteDiagonal, Matrix.diagonal_apply,
        Finset.sum_ite_eq'] <;> ring
    all_goals
      first
      | simpa [Matrix.transpose_apply] using congrArg
          (fun M : Matrix (Fin 5) (Fin 5) ℝ => M r c) ht
      | have hh := congrArg
          (fun M : Matrix (Fin 5) (Fin 5) ℝ => M r c) hb
        simp [Matrix.transpose_apply] at hh ⊢
        linarith⟩
  map_add' x y := by
    ext r c
    rcases r with r | r <;> rcases c with c | c <;> rfl
  map_smul' a x := by
    ext r c
    rcases r with r | r <;> rcases c with c | c <;> rfl

def topBlock5 (X : So55) : Skew5 :=
  ⟨fun i j => X.1 (Sum.inl i) (Sum.inl j), by
    have h := X.2
    change X.1 ∈ skewAdjointMatricesSubmodule D55 at h
    rw [mem_skewAdjointMatricesSubmodule] at h
    rw [mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_one, Matrix.one_mul]
    ext i j
    have hij := congr_fun (congr_fun h (Sum.inl i)) (Sum.inl j)
    simpa [D55, Matrix.mul_apply, LieAlgebra.Orthogonal.indefiniteDiagonal,
      Matrix.diagonal_apply, Finset.sum_ite_eq'] using hij⟩

def middleBlock5 (X : So55) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => X.1 (Sum.inl i) (Sum.inr j)

def bottomBlock5 (X : So55) : Skew5 :=
  ⟨fun i j => X.1 (Sum.inr i) (Sum.inr j), by
    have h := X.2
    change X.1 ∈ skewAdjointMatricesSubmodule D55 at h
    rw [mem_skewAdjointMatricesSubmodule] at h
    rw [mem_skewAdjointMatricesSubmodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair,
      Matrix.mul_one, Matrix.one_mul]
    ext i j
    have hij := congr_fun (congr_fun h (Sum.inr i)) (Sum.inr j)
    simp [D55, Matrix.mul_apply, LieAlgebra.Orthogonal.indefiniteDiagonal,
      Matrix.diagonal_apply, Finset.sum_ite_eq'] at hij ⊢
    linarith⟩

def blockFromSo55 : So55 →ₗ[ℝ] Block55 where
  toFun X := (topBlock5 X, middleBlock5 X, bottomBlock5 X)
  map_add' X Y := by ext <;> rfl
  map_smul' a X := by ext <;> rfl

def blockEquiv55 : So55 ≃ₗ[ℝ] Block55 where
  toFun := blockFromSo55
  invFun := blockToSo55
  left_inv X := by
    have h := X.2
    change X.1 ∈ skewAdjointMatricesSubmodule D55 at h
    rw [mem_skewAdjointMatricesSubmodule] at h
    apply Subtype.ext
    ext r c
    rcases r with r | r <;> rcases c with c | c <;>
      simp [blockToSo55, blockFromSo55, blockMatrix55, topBlock5, middleBlock5,
        bottomBlock5,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] at *
    all_goals
      first
      | rfl
      | have hrc := congr_fun (congr_fun h (Sum.inr r)) (Sum.inl c)
        simpa [D55, Matrix.mul_apply, LieAlgebra.Orthogonal.indefiniteDiagonal,
          Matrix.diagonal_apply, Finset.sum_ite_eq'] using hrc
  right_inv x := by
    ext r c
    rcases r with r | r <;> rcases c with c | c <;>
      simp [blockToSo55, blockFromSo55, blockMatrix55, topBlock5, middleBlock5,
        bottomBlock5,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;> rfl
    all_goals
      first
      | change x.2.1 r c = x.2.1 r c
        rfl
      | change (x.2.2.1 : Matrix (Fin 5) (Fin 5) ℝ) r c = x.2.2.1 r c
        rfl
  map_add' := blockFromSo55.map_add
  map_smul' := blockFromSo55.map_smul

theorem so55_finrank : Module.finrank ℝ So55 = 45 := by
  rw [blockEquiv55.finrank_eq, Module.finrank_prod, Module.finrank_prod,
    skewEquiv5.finrank_eq]
  simp [Module.finrank_matrix]

def tkkBlockEquiv : Block55 ≃ₗ[ℝ] TKKBlockCarrier :=
  LinearEquiv.prodCongr skewEquiv5
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ (Matrix (Fin 5) (Fin 5) ℝ)) skewEquiv5)

def so55TkkBlockEquiv : So55 ≃ₗ[ℝ] TKKBlockCarrier :=
  blockEquiv55.trans tkkBlockEquiv

theorem so55_tkk_block_finrank : Module.finrank ℝ So55 =
    Module.finrank ℝ TKKBlockCarrier := by
  exact so55TkkBlockEquiv.finrank_eq

theorem tkk_to_so55_finrank
    {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (e : L ≃ₗ⁅ℝ⁆ So55)
    (hSo55 : Module.finrank ℝ So55 = 45) :
    Module.finrank ℝ L = 45 := by
  calc
    Module.finrank ℝ L = Module.finrank ℝ So55 :=
      e.toLinearEquiv.finrank_eq
    _ = 45 := hSo55

abbrev TKKTypeD := LieAlgebra.Orthogonal.typeD (Fin 5) ℝ

noncomputable def tkkToSo55 : TKKTypeD ≃ₗ⁅ℝ⁆ So55 :=
  LieAlgebra.Orthogonal.typeDEquivSo' (Fin 5) ℝ

theorem tkkToSo55_map_lie (x y : TKKTypeD) :
    tkkToSo55 ⁅x, y⁆ = ⁅tkkToSo55 x, tkkToSo55 y⁆ := by
  exact tkkToSo55.map_lie x y

noncomputable def tkkTypeDBlockEquiv : TKKTypeD ≃ₗ[ℝ] TKKBlockCarrier :=
  tkkToSo55.toLinearEquiv.trans so55TkkBlockEquiv

theorem tkk_typeD_finrank : Module.finrank ℝ TKKTypeD = 45 := by
  rw [tkkTypeDBlockEquiv.finrank_eq, tkk_block_carrier_finrank]

theorem tkk_to_so55_lie_equivalence_finrank :
    Module.finrank ℝ TKKTypeD = Module.finrank ℝ So55 := by
  exact tkkToSo55.toLinearEquiv.finrank_eq

theorem tkk_inversion_swaps_outer_grades
    {J L : Type*} [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    (T : OperatorAlgebra.TKKLieClosure J L)
    (I : OperatorAlgebra.TKKInversionClosure J L T)
    (x : J) :
    I.inversion (T.neg x) = T.pos x ∧
      I.inversion (T.pos x) = T.neg x := by
  exact ⟨I.maps_neg_to_pos x, I.maps_pos_to_neg x⟩

theorem tkk_inversion_reflects_zero_grade
    {J L : Type*} [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    (T : OperatorAlgebra.TKKLieClosure J L)
    (I : OperatorAlgebra.TKKInversionClosure J L T)
    (x y : J) :
    I.inversion (T.zero x y) = -T.zero x y := by
  exact I.zero_grade_compatibility x y

theorem tkk_inversion_is_involution
    {J L : Type*} [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    (T : InfoGeometry.OperatorAlgebra.TKKLieClosure J L)
    (I : InfoGeometry.OperatorAlgebra.TKKInversionClosure J L T)
    (x : L) :
    I.inversion (I.inversion x) = x := by
  exact I.inversion_involutive x

theorem tkk_inversion_differs_from_grade_preserving_parity
    {J L : Type*} [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    (T : InfoGeometry.OperatorAlgebra.TKKLieClosure J L)
    (I : InfoGeometry.OperatorAlgebra.TKKInversionClosure J L T)
    (P : L ≃ₗ[ℝ] L) (x : J)
    (hP : P (T.neg x) = T.neg x)
    (hneq : T.pos x ≠ T.neg x) :
    I.inversion ≠ P := by
  intro hIP
  apply hneq
  calc
    T.pos x = I.inversion (T.neg x) := I.maps_neg_to_pos x |>.symm
    _ = P (T.neg x) := by rw [hIP]
    _ = T.neg x := hP

theorem mobius_parity_separate
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (mobius parity : Module.End ℝ V)
    (x : V) (h : mobius x ≠ parity x) : mobius ≠ parity := by
  intro e
  apply h
  rw [e]

end InfoGeometry.Canonical.SplitOctonionTKKFiniteDimensionalBridges
