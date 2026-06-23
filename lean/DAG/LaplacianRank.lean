import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.RankNullity

open Matrix

namespace DAG.LaplacianRank

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p]

def innerProduct (x y : m → ℚ) : ℚ := ∑ i, x i * y i

@[simp] lemma innerProduct_add (x y z : m → ℚ) : innerProduct x (y + z) = innerProduct x y + innerProduct x z := by
  dsimp [innerProduct]; simp [Finset.sum_add_distrib, mul_add]

lemma innerProduct_comm (x y : m → ℚ) : innerProduct x y = innerProduct y x := by
  dsimp [innerProduct]; apply Finset.sum_congr rfl; intro i _; ring

lemma innerProduct_self_nonneg (x : m → ℚ) : 0 ≤ innerProduct x x := by
  dsimp [innerProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

lemma innerProduct_self_eq_zero_iff (x : m → ℚ) : innerProduct x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h1 : ∀ i ∈ Finset.univ, 0 ≤ x i * x i := fun i _ => mul_self_nonneg (x i)
    have h2 : ∀ i ∈ Finset.univ, x i * x i = 0 := by
      intro i hi
      exact (Finset.sum_eq_zero_iff_of_nonneg h1).mp h i hi
    ext i
    exact eq_zero_of_mul_self_eq_zero (h2 i (Finset.mem_univ i))
  · intro h; subst h; simp [innerProduct]

lemma innerProduct_transpose_mulVec_eq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) (x : m → ℚ) (y : n → ℚ) :
    innerProduct x (A.mulVec y) = innerProduct (Aᵀ.mulVec x) y := by
  dsimp [innerProduct, mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  ring

lemma posSemidef_AAtranspose (A : Matrix m n ℚ) (x : m → ℚ) : 0 ≤ innerProduct x ((A * Aᵀ).mulVec x) := by
  have h_mul : (A * Aᵀ).mulVec x = A.mulVec (Aᵀ.mulVec x) := by rw [Matrix.mulVec_mulVec]
  rw [h_mul, innerProduct_transpose_mulVec_eq A x (Aᵀ.mulVec x)]
  exact innerProduct_self_nonneg (Aᵀ.mulVec x)

lemma posSemidef_BtransposeB (B : Matrix p m ℚ) (x : m → ℚ) : 0 ≤ innerProduct x ((Bᵀ * B).mulVec x) := by
  have h_mul : (Bᵀ * B).mulVec x = Bᵀ.mulVec (B.mulVec x) := by rw [Matrix.mulVec_mulVec]
  rw [h_mul, innerProduct_transpose_mulVec_eq Bᵀ x (B.mulVec x)]
  have h_trans : (Bᵀᵀ : Matrix p m ℚ) = B := Matrix.transpose_transpose B
  rw [h_trans]
  exact innerProduct_self_nonneg (B.mulVec x)

lemma orthogonal_ranges (A : Matrix m n ℚ) (B : Matrix p m ℚ) (hBA : B * A = 0) (x : n → ℚ) (y : p → ℚ) :
    innerProduct (A.mulVec x) (Bᵀ.mulVec y) = 0 := by
  have h1 : innerProduct (A.mulVec x) (Bᵀ.mulVec y) = innerProduct (Bᵀ.mulVec y) (A.mulVec x) := by rw [innerProduct_comm]
  have h2 : innerProduct (Bᵀ.mulVec y) (A.mulVec x) = innerProduct y (B.mulVec (A.mulVec x)) := by rw [innerProduct_transpose_mulVec_eq B y (A.mulVec x)]
  have h3 : innerProduct y (B.mulVec (A.mulVec x)) = innerProduct (B.mulVec (A.mulVec x)) y := by rw [innerProduct_comm]
  have h4 : innerProduct (B.mulVec (A.mulVec x)) y = innerProduct ((B * A).mulVec x) y := by rw [← Matrix.mulVec_mulVec]
  have h5 : innerProduct ((B * A).mulVec x) y = innerProduct ((0 : Matrix p n ℚ).mulVec x) y := by rw [hBA]
  rw [h1, h2, h3, h4, h5]; simp [innerProduct, mulVec]

lemma ker_laplacian_eq_inter_ker (A : Matrix m n ℚ) (B : Matrix p m ℚ) (hBA : B * A = 0) (x : m → ℚ) :
    ((A * Aᵀ + Bᵀ * B).mulVec x = 0) ↔ (Aᵀ.mulVec x = 0 ∧ B.mulVec x = 0) := by
  constructor
  · intro h
    have h0 : innerProduct x ((A * Aᵀ + Bᵀ * B).mulVec x) = 0 := by rw [h]; simp [innerProduct]
    rw [Matrix.add_mulVec, innerProduct_add] at h0
    have hposA : 0 ≤ innerProduct x ((A * Aᵀ).mulVec x) := posSemidef_AAtranspose A x
    have hposB : 0 ≤ innerProduct x ((Bᵀ * B).mulVec x) := posSemidef_BtransposeB B x
    have hA0 : innerProduct x ((A * Aᵀ).mulVec x) = 0 := by linarith
    have hB0 : innerProduct x ((Bᵀ * B).mulVec x) = 0 := by linarith
    have h_mulA : (A * Aᵀ).mulVec x = A.mulVec (Aᵀ.mulVec x) := by rw [Matrix.mulVec_mulVec]
    rw [h_mulA, innerProduct_transpose_mulVec_eq A x (Aᵀ.mulVec x)] at hA0
    have hA_tr : Aᵀ.mulVec x = 0 := (innerProduct_self_eq_zero_iff (Aᵀ.mulVec x)).mp hA0
    have h_mulB : (Bᵀ * B).mulVec x = Bᵀ.mulVec (B.mulVec x) := by rw [Matrix.mulVec_mulVec]
    rw [h_mulB, innerProduct_transpose_mulVec_eq Bᵀ x (B.mulVec x)] at hB0
    have h_trans : (Bᵀᵀ : Matrix p m ℚ) = B := Matrix.transpose_transpose B
    rw [h_trans] at hB0
    have hB_zero : B.mulVec x = 0 := (innerProduct_self_eq_zero_iff (B.mulVec x)).mp hB0
    exact ⟨hA_tr, hB_zero⟩
  · intro h_and
    have hA_tr : Aᵀ.mulVec x = 0 := h_and.1
    have hB_zero : B.mulVec x = 0 := h_and.2
    have h_mulA : (A * Aᵀ).mulVec x = A.mulVec (Aᵀ.mulVec x) := by rw [Matrix.mulVec_mulVec]
    have h_mulB : (Bᵀ * B).mulVec x = Bᵀ.mulVec (B.mulVec x) := by rw [Matrix.mulVec_mulVec]
    rw [Matrix.add_mulVec, h_mulA, h_mulB, hA_tr, hB_zero]
    simp [mulVec]

theorem laplacian_rank_eq_add_rank (A : Matrix m n ℚ) (B : Matrix p m ℚ) (hBA : B * A = 0) :
    Matrix.rank (A * Aᵀ + Bᵀ * B : Matrix m m ℚ) = Matrix.rank A + Matrix.rank B := by
  let C := A * Aᵀ; let D := Bᵀ * B
  have h_kerA : LinearMap.ker C.mulVecLin = LinearMap.ker Aᵀ.mulVecLin := by
    ext x; constructor
    · intro hx
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
      have hx_zero : C.mulVec x = 0 := hx
      have h_d : innerProduct x (C.mulVec x) = 0 := by rw [hx_zero]; simp [innerProduct]
      have h_mulA : C.mulVec x = A.mulVec (Aᵀ.mulVec x) := by dsimp [C]; rw [Matrix.mulVec_mulVec]
      rw [h_mulA] at h_d
      rw [innerProduct_transpose_mulVec_eq A x (Aᵀ.mulVec x)] at h_d
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact (innerProduct_self_eq_zero_iff (Aᵀ.mulVec x)).mp h_d
    · intro hx
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
      have h_mulA : C.mulVec x = A.mulVec (Aᵀ.mulVec x) := by dsimp [C]; rw [Matrix.mulVec_mulVec]
      rw [h_mulA, hx, Matrix.mulVec_zero]
  have h1A := LinearMap.finrank_range_add_finrank_ker C.mulVecLin
  have h2A := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  have h_cardA : Module.finrank ℚ (m → ℚ) = Fintype.card m := by simp
  rw [h_cardA] at h1A h2A
  rw [← Matrix.rank] at h1A h2A
  rw [Matrix.rank_transpose] at h2A
  rw [h_kerA] at h1A
  have hC_rank : Matrix.rank C = Matrix.rank A := by omega

  have h_kerB : LinearMap.ker D.mulVecLin = LinearMap.ker B.mulVecLin := by
    ext x; constructor
    · intro hx
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx
      have h_d : innerProduct x (D.mulVec x) = 0 := by rw [hx]; simp [innerProduct]
      have h_mulB : D.mulVec x = Bᵀ.mulVec (B.mulVec x) := by dsimp [D]; rw [Matrix.mulVec_mulVec]
      rw [h_mulB] at h_d
      rw [innerProduct_transpose_mulVec_eq Bᵀ x (B.mulVec x)] at h_d
      have h_trans : (Bᵀᵀ : Matrix p m ℚ) = B := Matrix.transpose_transpose B
      rw [h_trans] at h_d
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact (innerProduct_self_eq_zero_iff (B.mulVec x)).mp h_d
    · intro hx
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
      have h_mulB : D.mulVec x = Bᵀ.mulVec (B.mulVec x) := by dsimp [D]; rw [Matrix.mulVec_mulVec]
      rw [h_mulB, hx, Matrix.mulVec_zero]
  have h1B := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  have h2B := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have h_cardB : Module.finrank ℚ (m → ℚ) = Fintype.card m := by simp
  rw [h_cardB] at h1B h2B
  rw [← Matrix.rank] at h1B h2B
  rw [h_kerB] at h1B
  have hD_rank : Matrix.rank D = Matrix.rank B := by omega

  have hC_sym : Cᵀ = C := by dsimp [C]; simp
  have hD_sym : Dᵀ = D := by dsimp [D]; simp
  have h_CD : C * D = 0 := by
    have step1 : C * D = A * Aᵀ * Bᵀ * B := by simp [C, D, Matrix.mul_assoc]
    have step2 : A * Aᵀ * Bᵀ * B = A * ((B * A)ᵀ) * B := by simp [Matrix.mul_assoc]
    have step3 : A * ((B * A)ᵀ) * B = A * (0 : Matrix p n ℚ)ᵀ * B := by rw [hBA]
    have step4 : A * (0 : Matrix p n ℚ)ᵀ * B = 0 := by simp
    rw [step1, step2, step3, step4]
  have h_DC : D * C = 0 := by
    have step1 : D * C = Dᵀ * Cᵀ := by rw [hD_sym, hC_sym]
    have step2 : Dᵀ * Cᵀ = (C * D)ᵀ := (Matrix.transpose_mul C D).symm
    have step3 : (C * D)ᵀ = (0 : Matrix m m ℚ)ᵀ := by rw [h_CD]
    have step4 : (0 : Matrix m m ℚ)ᵀ = 0 := Matrix.transpose_zero
    rw [step1, step2, step3, step4]
  have h_inter : LinearMap.range C.mulVecLin ⊓ LinearMap.range D.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rcases Submodule.mem_inf.mp hv with ⟨hvC, hvD⟩
    rcases LinearMap.mem_range.mp hvC with ⟨x, hx⟩
    rcases LinearMap.mem_range.mp hvD with ⟨y, hy⟩
    simp only [Matrix.mulVecLin_apply] at hx hy
    have h_Dv : D.mulVec v = 0 := by
      have h_mulDC : (D * C).mulVec x = D.mulVec (C.mulVec x) := by rw [Matrix.mulVec_mulVec]
      rw [← hx, ← h_mulDC, h_DC, Matrix.zero_mulVec]
    have h_mulDD : (D * D).mulVec y = D.mulVec (D.mulVec y) := by rw [Matrix.mulVec_mulVec]
    rw [← hy, ← h_mulDD] at h_Dv
    have h_dy : innerProduct y ((D * D).mulVec y) = 0 := by rw [h_Dv]; simp [innerProduct]
    have h_norm : innerProduct (D.mulVec y) (D.mulVec y) = 0 := by
      have step1 : innerProduct (D.mulVec y) (D.mulVec y) = innerProduct (Dᵀ.mulVec y) (D.mulVec y) := by rw [hD_sym]
      have step2 : innerProduct (Dᵀ.mulVec y) (D.mulVec y) = innerProduct y (D.mulVec (D.mulVec y)) := (innerProduct_transpose_mulVec_eq D y (D.mulVec y)).symm
      have h_mul_D_y : (D * D).mulVec y = D.mulVec (D.mulVec y) := by rw [Matrix.mulVec_mulVec]
      have step3 : innerProduct y (D.mulVec (D.mulVec y)) = innerProduct y ((D * D).mulVec y) := by rw [← h_mul_D_y]
      rw [step1, step2, step3, h_dy]
    have hDy : D.mulVec y = 0 := (innerProduct_self_eq_zero_iff (D.mulVec y)).mp h_norm
    rw [← hy]
    exact hDy
  have h_im_Csq : LinearMap.range (C * C).mulVecLin = LinearMap.range C.mulVecLin := by
    have h_sub : LinearMap.range (C * C).mulVecLin ≤ LinearMap.range C.mulVecLin := by
      intro v hv'; rcases LinearMap.mem_range.mp hv' with ⟨z, hz⟩
      refine LinearMap.mem_range.mpr ⟨C.mulVec z, ?_⟩
      simp only [Matrix.mulVecLin_apply] at hz ⊢
      have h_mulCC : (C * C).mulVec z = C.mulVec (C.mulVec z) := by rw [Matrix.mulVec_mulVec]
      rw [← h_mulCC, hz]
    have h_ker_sq : LinearMap.ker (C * C).mulVecLin = LinearMap.ker C.mulVecLin := by
      ext z; constructor
      · intro hz'
        simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz'
        have h_dz : innerProduct z ((C * C).mulVec z) = 0 := by rw [hz']; simp [innerProduct]
        have h_nz : innerProduct (C.mulVec z) (C.mulVec z) = 0 := by
          have step1 : innerProduct (C.mulVec z) (C.mulVec z) = innerProduct (Cᵀ.mulVec z) (C.mulVec z) := by rw [hC_sym]
          have step2 : innerProduct (Cᵀ.mulVec z) (C.mulVec z) = innerProduct z (C.mulVec (C.mulVec z)) := (innerProduct_transpose_mulVec_eq C z (C.mulVec z)).symm
          have h_mul_C_z : (C * C).mulVec z = C.mulVec (C.mulVec z) := by rw [Matrix.mulVec_mulVec]
          have step3 : innerProduct z (C.mulVec (C.mulVec z)) = innerProduct z ((C * C).mulVec z) := by rw [← h_mul_C_z]
          rw [step1, step2, step3, h_dz]
        simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact (innerProduct_self_eq_zero_iff (C.mulVec z)).mp h_nz
      · intro hz'
        simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz' ⊢
        have h_mulCC : (C * C).mulVec z = C.mulVec (C.mulVec z) := by rw [Matrix.mulVec_mulVec]
        rw [h_mulCC, hz', Matrix.mulVec_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker (C * C).mulVecLin
    have h2 := LinearMap.finrank_range_add_finrank_ker C.mulVecLin
    have h_card_m2 : Module.finrank ℚ (m → ℚ) = Fintype.card m := by simp
    rw [h_card_m2] at h1 h2
    rw [h_ker_sq] at h1
    have h_finrank_eq : Module.finrank ℚ (LinearMap.range (C * C).mulVecLin) = Module.finrank ℚ (LinearMap.range C.mulVecLin) := by omega
    exact Submodule.eq_of_le_of_finrank_eq h_sub h_finrank_eq
  have h_im_Dsq : LinearMap.range (D * D).mulVecLin = LinearMap.range D.mulVecLin := by
    have h_sub : LinearMap.range (D * D).mulVecLin ≤ LinearMap.range D.mulVecLin := by
      intro v hv'; rcases LinearMap.mem_range.mp hv' with ⟨z, hz⟩
      refine LinearMap.mem_range.mpr ⟨D.mulVec z, ?_⟩
      simp only [Matrix.mulVecLin_apply] at hz ⊢
      have h_mulDD : (D * D).mulVec z = D.mulVec (D.mulVec z) := by rw [Matrix.mulVec_mulVec]
      rw [← h_mulDD, hz]
    have h_ker_sq : LinearMap.ker (D * D).mulVecLin = LinearMap.ker D.mulVecLin := by
      ext z; constructor
      · intro hz'
        simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz'
        have h_dz : innerProduct z ((D * D).mulVec z) = 0 := by rw [hz']; simp [innerProduct]
        have h_nz : innerProduct (D.mulVec z) (D.mulVec z) = 0 := by
          have step1 : innerProduct (D.mulVec z) (D.mulVec z) = innerProduct (Dᵀ.mulVec z) (D.mulVec z) := by rw [hD_sym]
          have step2 : innerProduct (Dᵀ.mulVec z) (D.mulVec z) = innerProduct z (D.mulVec (D.mulVec z)) := (innerProduct_transpose_mulVec_eq D z (D.mulVec z)).symm
          have h_mul_D_z : (D * D).mulVec z = D.mulVec (D.mulVec z) := by rw [Matrix.mulVec_mulVec]
          have step3 : innerProduct z (D.mulVec (D.mulVec z)) = innerProduct z ((D * D).mulVec z) := by rw [← h_mul_D_z]
          rw [step1, step2, step3, h_dz]
        simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact (innerProduct_self_eq_zero_iff (D.mulVec z)).mp h_nz
      · intro hz'
        simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hz' ⊢
        have h_mulDD : (D * D).mulVec z = D.mulVec (D.mulVec z) := by rw [Matrix.mulVec_mulVec]
        rw [h_mulDD, hz', Matrix.mulVec_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker (D * D).mulVecLin
    have h2 := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
    have h_card_m2 : Module.finrank ℚ (m → ℚ) = Fintype.card m := by simp
    rw [h_card_m2] at h1 h2
    rw [h_ker_sq] at h1
    have h_finrank_eq : Module.finrank ℚ (LinearMap.range (D * D).mulVecLin) = Module.finrank ℚ (LinearMap.range D.mulVecLin) := by omega
    exact Submodule.eq_of_le_of_finrank_eq h_sub h_finrank_eq
  have h_imC_sub : LinearMap.range C.mulVecLin ≤ LinearMap.range (C + D).mulVecLin := by
    intro v hv
    have h_in_C2 : v ∈ LinearMap.range (C * C).mulVecLin := by rw [h_im_Csq]; exact hv
    rcases LinearMap.mem_range.mp h_in_C2 with ⟨y, hy⟩
    refine LinearMap.mem_range.mpr ⟨C.mulVec y, ?_⟩
    simp only [Matrix.mulVecLin_apply] at hy ⊢
    have h_mulCC : (C * C).mulVec y = C.mulVec (C.mulVec y) := by rw [Matrix.mulVec_mulVec]
    have h_mulDC : (D * C).mulVec y = D.mulVec (C.mulVec y) := by rw [Matrix.mulVec_mulVec]
    have step1 : (C + D).mulVec (C.mulVec y) = C.mulVec (C.mulVec y) + D.mulVec (C.mulVec y) := by rw [Matrix.add_mulVec]
    have step2 : C.mulVec (C.mulVec y) + D.mulVec (C.mulVec y) = (C * C).mulVec y + (D * C).mulVec y := by rw [← h_mulCC, ← h_mulDC]
    have step3 : (C * C).mulVec y + (D * C).mulVec y = (C * C).mulVec y + (0 : Matrix m m ℚ).mulVec y := by rw [h_DC]
    have step4 : (C * C).mulVec y + (0 : Matrix m m ℚ).mulVec y = (C * C).mulVec y + 0 := by rw [Matrix.zero_mulVec]
    have step5 : (C * C).mulVec y + 0 = v := by simp [hy]
    rw [step1, step2, step3, step4, step5]
  have h_imD_sub : LinearMap.range D.mulVecLin ≤ LinearMap.range (C + D).mulVecLin := by
    intro v hv
    have h_in_D2 : v ∈ LinearMap.range (D * D).mulVecLin := by rw [h_im_Dsq]; exact hv
    rcases LinearMap.mem_range.mp h_in_D2 with ⟨z, hz⟩
    refine LinearMap.mem_range.mpr ⟨D.mulVec z, ?_⟩
    simp only [Matrix.mulVecLin_apply] at hz ⊢
    have h_mulDD : (D * D).mulVec z = D.mulVec (D.mulVec z) := by rw [Matrix.mulVec_mulVec]
    have h_mulCD : (C * D).mulVec z = C.mulVec (D.mulVec z) := by rw [Matrix.mulVec_mulVec]
    have step1 : (C + D).mulVec (D.mulVec z) = C.mulVec (D.mulVec z) + D.mulVec (D.mulVec z) := by rw [Matrix.add_mulVec]
    have step2 : C.mulVec (D.mulVec z) + D.mulVec (D.mulVec z) = (C * D).mulVec z + (D * D).mulVec z := by rw [← h_mulCD, ← h_mulDD]
    have step3 : (C * D).mulVec z + (D * D).mulVec z = (0 : Matrix m m ℚ).mulVec z + (D * D).mulVec z := by rw [h_CD]
    have step4 : (0 : Matrix m m ℚ).mulVec z + (D * D).mulVec z = 0 + (D * D).mulVec z := by rw [Matrix.zero_mulVec]
    have step5 : 0 + (D * D).mulVec z = v := by simp [hz]
    rw [step1, step2, step3, step4, step5]
  have h_range : LinearMap.range (C + D).mulVecLin = LinearMap.range C.mulVecLin ⊔ LinearMap.range D.mulVecLin := by
    apply le_antisymm
    · intro v hv; rcases LinearMap.mem_range.mp hv with ⟨x, hx⟩
      simp only [Matrix.mulVecLin_apply] at hx
      have h_add : (C + D).mulVec x = C.mulVec x + D.mulVec x := by rw [Matrix.add_mulVec]
      rw [h_add] at hx
      rw [← hx]
      apply Submodule.add_mem_sup
      · exact LinearMap.mem_range.mpr ⟨x, rfl⟩
      · exact LinearMap.mem_range.mpr ⟨x, rfl⟩
    · exact sup_le h_imC_sub h_imD_sub
  have h_dim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range C.mulVecLin) (LinearMap.range D.mulVecLin)
  rw [h_inter] at h_dim
  have h_bot : Module.finrank ℚ ↥(⊥ : Submodule ℚ (m → ℚ)) = 0 := Submodule.finrank_eq_zero.mpr rfl
  rw [h_bot, add_zero] at h_dim
  have h_rank_sum : Matrix.rank (A * Aᵀ + Bᵀ * B) = Module.finrank ℚ (LinearMap.range (C + D).mulVecLin) := rfl
  have h_rC : Module.finrank ℚ (LinearMap.range C.mulVecLin) = Matrix.rank C := rfl
  have h_rD : Module.finrank ℚ (LinearMap.range D.mulVecLin) = Matrix.rank D := rfl
  rw [h_rank_sum, h_range, h_dim, h_rC, h_rD, hC_rank, hD_rank]

theorem ker_trivial_when_full_rank (A : Matrix m n ℚ) (B : Matrix p m ℚ) (hBA : B * A = 0)
    (h_full : Matrix.rank A + Matrix.rank B = Fintype.card m) (x : m → ℚ)
    (hx : (A * Aᵀ + Bᵀ * B).mulVec x = 0) : x = 0 := by
  have h_ker_eq := (ker_laplacian_eq_inter_ker A B hBA x).mp hx
  have hA_tr : Aᵀ.mulVec x = 0 := h_ker_eq.1
  have hB_zero : B.mulVec x = 0 := h_ker_eq.2
  have h_rank_laplacian : Matrix.rank (A * Aᵀ + Bᵀ * B : Matrix m m ℚ) = Fintype.card m := by
    rw [laplacian_rank_eq_add_rank A B hBA, h_full]
  have h_RK : Matrix.rank (A * Aᵀ + Bᵀ * B : Matrix m m ℚ) + Module.finrank ℚ (LinearMap.ker (A * Aᵀ + Bᵀ * B : Matrix m m ℚ).mulVecLin) = Fintype.card m := by
    have h := LinearMap.finrank_range_add_finrank_ker (A * Aᵀ + Bᵀ * B : Matrix m m ℚ).mulVecLin
    have h_card : Module.finrank ℚ (m → ℚ) = Fintype.card m := by simp
    rw [h_card, ← Matrix.rank] at h; omega
  rw [h_rank_laplacian] at h_RK
  have h_ker_dim : Module.finrank ℚ (LinearMap.ker (A * Aᵀ + Bᵀ * B : Matrix m m ℚ).mulVecLin) = 0 := by omega
  have h_ker_trivial : LinearMap.ker (A * Aᵀ + Bᵀ * B : Matrix m m ℚ).mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp h_ker_dim
  have hx_ker : x ∈ LinearMap.ker (A * Aᵀ + Bᵀ * B : Matrix m m ℚ).mulVecLin := by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hx
  rw [h_ker_trivial] at hx_ker
  exact hx_ker

end DAG.LaplacianRank
