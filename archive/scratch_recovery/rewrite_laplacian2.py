content = """import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.RankNullity

open Matrix

namespace DAG.LaplacianRank

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dotProduct (x y : m → ℚ) : ℚ := ∑ i, x i * y i

@[simp] lemma dotProduct_add (x y z : m → ℚ) : dotProduct x (y + z) = dotProduct x y + dotProduct x z := by
  dsimp [dotProduct]; simp [Finset.sum_add_distrib, mul_add]

lemma dotProduct_self_nonneg (x : m → ℚ) : 0 ≤ dotProduct x x := by
  dsimp [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

lemma dotProduct_self_eq_zero_iff (x : m → ℚ) : dotProduct x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h1 : ∀ i ∈ Finset.univ, 0 ≤ x i * x i := fun i _ => mul_self_nonneg (x i)
    have h2 : ∀ i ∈ Finset.univ, x i * x i = 0 := by
      intro i hi
      exact (Finset.sum_eq_zero_iff_of_nonneg h1).mp h i hi
    ext i
    exact eq_zero_of_mul_self_eq_zero (h2 i (Finset.mem_univ i))
  · intro h; subst h; simp [dotProduct]

lemma dotProduct_transpose_mulVec_eq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) (x : m → ℚ) (y : n → ℚ) :
    dotProduct x (A.mulVec y) = dotProduct (Aᵀ.mulVec x) y := by
  simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum, transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro i _
  ring

lemma posSemidef_AAtranspose (A : Matrix m n ℚ) (x : m → ℚ) : 0 ≤ dotProduct x ((A * Aᵀ).mulVec x) := by
  rw [← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec_eq A x (Aᵀ.mulVec x)]
  exact dotProduct_self_nonneg (Aᵀ.mulVec x)

lemma posSemidef_BtransposeB (B : Matrix p m ℚ) (x : m → ℚ) : 0 ≤ dotProduct x ((Bᵀ * B).mulVec x) := by
  rw [← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec_eq Bᵀ x (B.mulVec x)]
  have h_trans : (Bᵀᵀ : Matrix p m ℚ) = B := Matrix.transpose_transpose B
  rw [h_trans]
  exact dotProduct_self_nonneg (B.mulVec x)

lemma orthogonal_ranges (A : Matrix m n ℚ) (B : Matrix p m ℚ) (hBA : B * A = 0) (x : n → ℚ) (y : p → ℚ) :
    dotProduct (A.mulVec x) (Bᵀ.mulVec y) = 0 := by
  calc
    dotProduct (A.mulVec x) (Bᵀ.mulVec y) = dotProduct (B.mulVec (A.mulVec x)) y := by
      rw [dotProduct_transpose_mulVec_eq B (A.mulVec x) y]
    _ = dotProduct ((B * A).mulVec x) y := by rw [Matrix.mulVec_mulVec]
    _ = dotProduct ((0 : Matrix p n ℚ).mulVec x) y := by rw [hBA]
    _ = 0 := by simp [dotProduct, mulVec]

lemma ker_laplacian_eq_inter_ker (A : Matrix m n ℚ) (B : Matrix p m ℚ) (hBA : B * A = 0) (x : m → ℚ) :
    ((A * Aᵀ + Bᵀ * B).mulVec x = 0) ↔ (Aᵀ.mulVec x = 0 ∧ B.mulVec x = 0) := by
  constructor
  · intro h
    have h0 : dotProduct x ((A * Aᵀ + Bᵀ * B).mulVec x) = 0 := by rw [h]; simp [dotProduct]
    rw [Matrix.add_mulVec, dotProduct_add] at h0
    have hposA : 0 ≤ dotProduct x ((A * Aᵀ).mulVec x) := posSemidef_AAtranspose A x
    have hposB : 0 ≤ dotProduct x ((Bᵀ * B).mulVec x) := posSemidef_BtransposeB B x
    have hA0 : dotProduct x ((A * Aᵀ).mulVec x) = 0 := by linarith
    have hB0 : dotProduct x ((Bᵀ * B).mulVec x) = 0 := by linarith
    rw [← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec_eq A x (Aᵀ.mulVec x)] at hA0
    have hAᵀ : Aᵀ.mulVec x = 0 := (dotProduct_self_eq_zero_iff (Aᵀ.mulVec x)).mp hA0
    rw [← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec_eq Bᵀ x (B.mulVec x)] at hB0
    have h_trans : (Bᵀᵀ : Matrix p m ℚ) = B := Matrix.transpose_transpose B
    rw [h_trans] at hB0
    have hB : B.mulVec x = 0 := (dotProduct_self_eq_zero_iff (B.mulVec x)).mp hB0
    exact ⟨hAᵀ, hB⟩
  · intro ⟨hA_tr, hB⟩; rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA_tr, hB]; simp [mulVec]

theorem laplacian_rank_eq_add_rank (A : Matrix m n ℚ) (B : Matrix p m ℚ) (hBA : B * A = 0) :
    Matrix.rank (A * Aᵀ + Bᵀ * B : Matrix m m ℚ) = Matrix.rank A + Matrix.rank B := by
  let C := A * Aᵀ; let D := Bᵀ * B
  have h_card_m : Module.finrank ℚ (m → ℚ) = Fintype.card m := by simp
  have h_RK {k : Type*} [Fintype k] [DecidableEq k] (M : Matrix k k ℚ) : Matrix.rank M + Module.finrank ℚ (LinearMap.ker M.mulVecLin) = Fintype.card k := by
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have h_card_k : Module.finrank ℚ (k → ℚ) = Fintype.card k := by simp
    rw [h_card_k, ← Matrix.rank] at h; exact h
  -- rank(X*Xᵀ) = rank(X)
  have h_rank_XXᵀ {k : Type*} [Fintype k] [DecidableEq k] (X : Matrix m k ℚ) : Matrix.rank (X * Xᵀ) = Matrix.rank X := by
    have h_ker_eq : LinearMap.ker (X * Xᵀ).mulVecLin = LinearMap.ker (Xᵀ : Matrix m k ℚ).mulVecLin := by
      ext x; constructor
      · intro hx; have h_d : dotProduct x ((X * Xᵀ).mulVec x) = 0 := by simp [LinearMap.mem_ker.mp hx, dotProduct]
        rw [← Matrix.mulVec_mulVec] at h_d
        rw [dotProduct_transpose_mulVec_eq X x (Xᵀ.mulVec x)] at h_d
        rw [LinearMap.mem_ker]; exact (dotProduct_self_eq_zero_iff (Xᵀ.mulVec x)).mp h_d
      · intro hx; rw [← Matrix.mulVec_mulVec]; simp [LinearMap.mem_ker.mp hx, mulVec]
    have h1 := h_RK (X * Xᵀ)
    have h2 : Matrix.rank Xᵀ + Module.finrank ℚ (LinearMap.ker (Xᵀ : Matrix m k ℚ).mulVecLin) = Fintype.card m := by
      have h := LinearMap.finrank_range_add_finrank_ker (Xᵀ : Matrix m k ℚ).mulVecLin
      rw [h_card_m, ← Matrix.rank] at h; exact h
    rw [Matrix.rank_transpose] at h2
    rw [h_ker_eq] at h1; omega
  have hC_rank : Matrix.rank C = Matrix.rank A := h_rank_XXᵀ A
  have hD_rank : Matrix.rank D = Matrix.rank B := by simpa [D] using h_rank_XXᵀ Bᵀ
  have hC_sym : Cᵀ = C := by dsimp [C]; simp
  have hD_sym : Dᵀ = D := by dsimp [D]; simp
  have h_CD : C * D = 0 := by
    calc C * D = A * Aᵀ * Bᵀ * B := by simp [C, D, Matrix.mul_assoc]
      _ = A * ((B * A)ᵀ) * B := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [hBA]; simp
  have h_DC : D * C = 0 := by rw [hD_sym, hC_sym, ← Matrix.transpose_mul, h_CD, Matrix.transpose_zero]
  have h_inter : LinearMap.range C.mulVecLin ⊓ LinearMap.range D.mulVecLin = ⊥ := by
    apply Submodule.eq_bot_iff.mpr; intro v hv
    rcases Submodule.mem_inf.mp hv with ⟨hvC, hvD⟩
    rcases LinearMap.mem_range.mp hvC with ⟨x, hx⟩
    rcases LinearMap.mem_range.mp hvD with ⟨y, hy⟩
    have h_Dv : D.mulVec v = 0 := by rw [hx, ← Matrix.mulVec_mulVec, h_DC, Matrix.zero_mulVec]
    rw [hy, ← Matrix.mulVec_mulVec] at h_Dv
    have h_dy : dotProduct y (D.mulVec (D.mulVec y)) = 0 := by rw [h_Dv]; simp [dotProduct]
    have h_norm : dotProduct (D.mulVec y) (D.mulVec y) = 0 := by
      calc dotProduct y (D.mulVec (D.mulVec y)) = dotProduct (Dᵀ.mulVec y) (D.mulVec y) := by
        rw [dotProduct_transpose_mulVec_eq D y (D.mulVec y)]
      _ = dotProduct (D.mulVec y) (D.mulVec y) := by rw [hD_sym]
    rw [h_norm] at h_dy
    have hDy : D.mulVec y = 0 := (dotProduct_self_eq_zero_iff (D.mulVec y)).mp (by rw [← h_dy])
    rw [hy, hDy, mulVec_apply] at hv; exact Submodule.mem_bot.mpr hv
  have h_im_Csq : LinearMap.range (C * C).mulVecLin = LinearMap.range C.mulVecLin := by
    have h_sub : LinearMap.range (C * C).mulVecLin ≤ LinearMap.range C.mulVecLin := by
      intro v hv'; rcases LinearMap.mem_range.mp hv' with ⟨z, hz⟩
      refine LinearMap.mem_range.mpr ⟨C.mulVec z, ?_⟩; rw [← Matrix.mulVec_mulVec]; exact hz
    have h_ker_sq : LinearMap.ker (C * C).mulVecLin = LinearMap.ker C.mulVecLin := by
      ext z; constructor
      · intro hz'; have h_dz : dotProduct z ((C * C).mulVec z) = 0 := by simp [LinearMap.mem_ker.mp hz', dotProduct]
        rw [← Matrix.mulVec_mulVec] at h_dz
        have h_nz : dotProduct (C.mulVec z) (C.mulVec z) = 0 := by
          calc dotProduct z (C.mulVec (C.mulVec z)) = dotProduct (Cᵀ.mulVec z) (C.mulVec z) := by
            rw [dotProduct_transpose_mulVec_eq C z (C.mulVec z)]
          _ = dotProduct (C.mulVec z) (C.mulVec z) := by rw [hC_sym]
        rw [h_nz] at h_dz; rw [LinearMap.mem_ker]
        exact (dotProduct_self_eq_zero_iff (C.mulVec z)).mp (by rw [← h_dz])
      · intro hz'; rw [← Matrix.mulVec_mulVec, LinearMap.mem_ker.mp hz']; simp [mulVec]
    have h1 := h_RK (C * C); have h2 := h_RK C; rw [h_ker_sq] at h1; omega
    have h_finrank_eq : Module.finrank ℚ (LinearMap.range (C * C).mulVecLin) =
                       Module.finrank ℚ (LinearMap.range C.mulVecLin) := by
      rw [← Matrix.rank, ← Matrix.rank, h1]
    exact Submodule.eq_of_le_of_finrank_eq h_sub h_finrank_eq
  have h_im_Dsq : LinearMap.range (D * D).mulVecLin = LinearMap.range D.mulVecLin := by
    have h_sub : LinearMap.range (D * D).mulVecLin ≤ LinearMap.range D.mulVecLin := by
      intro v hv'; rcases LinearMap.mem_range.mp hv' with ⟨z, hz⟩
      refine LinearMap.mem_range.mpr ⟨D.mulVec z, ?_⟩; rw [← Matrix.mulVec_mulVec]; exact hz
    have h_ker_sq : LinearMap.ker (D * D).mulVecLin = LinearMap.ker D.mulVecLin := by
      ext z; constructor
      · intro hz'; have h_dz : dotProduct z ((D * D).mulVec z) = 0 := by simp [LinearMap.mem_ker.mp hz', dotProduct]
        rw [← Matrix.mulVec_mulVec] at h_dz
        have h_nz : dotProduct (D.mulVec z) (D.mulVec z) = 0 := by
          calc dotProduct z (D.mulVec (D.mulVec z)) = dotProduct (Dᵀ.mulVec z) (D.mulVec z) := by
            rw [dotProduct_transpose_mulVec_eq D z (D.mulVec z)]
          _ = dotProduct (D.mulVec z) (D.mulVec z) := by rw [hD_sym]
        rw [h_nz] at h_dz; rw [LinearMap.mem_ker]
        exact (dotProduct_self_eq_zero_iff (D.mulVec z)).mp (by rw [← h_dz])
      · intro hz'; rw [← Matrix.mulVec_mulVec, LinearMap.mem_ker.mp hz']; simp [mulVec]
    have h1 := h_RK (D * D); have h2 := h_RK D; rw [h_ker_sq] at h1; omega
    have h_finrank_eq : Module.finrank ℚ (LinearMap.range (D * D).mulVecLin) =
                       Module.finrank ℚ (LinearMap.range D.mulVecLin) := by
      rw [← Matrix.rank, ← Matrix.rank, h1]
    exact Submodule.eq_of_le_of_finrank_eq h_sub h_finrank_eq
  have h_imC_sub : LinearMap.range C.mulVecLin ≤ LinearMap.range (C + D).mulVecLin := by
    intro v hv; rcases LinearMap.mem_range.mp hv with ⟨x, hx⟩
    have h_in_C2 : C.mulVec x ∈ LinearMap.range (C * C).mulVecLin := by rw [h_im_Csq]; exact hv
    rcases LinearMap.mem_range.mp h_in_C2 with ⟨y, hy⟩
    refine LinearMap.mem_range.mpr ⟨C.mulVec y, ?_⟩
    calc (C + D).mulVec (C.mulVec y) = C.mulVec (C.mulVec y) + D.mulVec (C.mulVec y) := by simp [Matrix.add_mulVec]
      _ = (C * C).mulVec y + D.mulVec (C.mulVec y) := by rw [← Matrix.mulVec_mulVec]
      _ = (C * C).mulVec y + 0 := by rw [← Matrix.mulVec_mulVec, h_DC, Matrix.zero_mulVec]
      _ = (C * C).mulVec y := by simp
      _ = v := by rw [← hy, hx]
  have h_imD_sub : LinearMap.range D.mulVecLin ≤ LinearMap.range (C + D).mulVecLin := by
    intro v hv; rcases LinearMap.mem_range.mp hv with ⟨y, hy⟩
    have h_in_D2 : D.mulVec y ∈ LinearMap.range (D * D).mulVecLin := by rw [h_im_Dsq]; exact hv
    rcases LinearMap.mem_range.mp h_in_D2 with ⟨z, hz⟩
    refine LinearMap.mem_range.mpr ⟨D.mulVec z, ?_⟩
    calc (C + D).mulVec (D.mulVec z) = C.mulVec (D.mulVec z) + D.mulVec (D.mulVec z) := by simp [Matrix.add_mulVec]
      _ = 0 + (D * D).mulVec z := by rw [← Matrix.mulVec_mulVec, h_CD, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
      _ = (D * D).mulVec z := by simp
      _ = v := by rw [← hz, hy]
  have h_range : LinearMap.range (C + D).mulVecLin = LinearMap.range C.mulVecLin ⊔ LinearMap.range D.mulVecLin := by
    apply le_antisymm
    · intro v hv; rcases LinearMap.mem_range.mp hv with ⟨x, hx⟩
      rw [Matrix.add_mulVec] at hx
      exact Submodule.add_mem_sup (LinearMap.mem_range.mpr ⟨x, rfl⟩) (LinearMap.mem_range.mpr ⟨x, rfl⟩)
    · exact Submodule.sup_le h_imC_sub h_imD_sub
  rw [Matrix.rank, Matrix.rank, Matrix.rank, h_range]
  rw [Submodule.finrank_sup_add_finrank_inf_eq, h_inter, finrank_bot, add_zero, hC_rank, hD_rank]

theorem ker_trivial_when_full_rank (A : Matrix m n ℚ) (B : Matrix p m ℚ) (hBA : B * A = 0)
    (h_full : Matrix.rank A + Matrix.rank B = Fintype.card m) (x : m → ℚ)
    (hx : (A * Aᵀ + Bᵀ * B).mulVec x = 0) : x = 0 := by
  rcases (ker_laplacian_eq_inter_ker A B hBA x).mp hx with ⟨hA_tr, hB⟩
  have h_rank_laplacian : Matrix.rank (A * Aᵀ + Bᵀ * B : Matrix m m ℚ) = Fintype.card m := by
    rw [laplacian_rank_eq_add_rank A B hBA, h_full]
  have h_RK (M : Matrix m m ℚ) : Matrix.rank M + Module.finrank ℚ (LinearMap.ker M.mulVecLin) = Fintype.card m := by
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have h_card : Module.finrank ℚ (m → ℚ) = Fintype.card m := by simp
    rw [h_card, ← Matrix.rank] at h; omega
  have hK := h_RK (A * Aᵀ + Bᵀ * B : Matrix m m ℚ)
  rw [h_rank_laplacian] at hK
  have h_ker_dim : Module.finrank ℚ (LinearMap.ker (A * Aᵀ + Bᵀ * B : Matrix m m ℚ).mulVecLin) = 0 := by omega
  have h_ker_trivial : LinearMap.ker (A * Aᵀ + Bᵀ * B : Matrix m m ℚ).mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp h_ker_dim
  have hx_ker : x ∈ LinearMap.ker (A * Aᵀ + Bᵀ * B : Matrix m m ℚ).mulVecLin := by rw [LinearMap.mem_ker]; exact hx
  rw [h_ker_trivial] at hx_ker
  exact Submodule.mem_bot.mp hx_ker

end DAG.LaplacianRank
"""

with open("lean/DAG/LaplacianRank.lean", "w") as f:
    f.write(content)
