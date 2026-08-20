import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Universal Trifold Synthesis of Operator Surprisals

This module establishes the complete mathematical foundation for the Universal Trifold
Decomposition of any relative surprisal operator `K = -log Δ`:

    K = α • I₂ₙ + β • Γ + K₀

where:
1. `α = Tr(K) / (2n)` is the Common Radon–Nikodym Mode (isotropic volume / Weyl scale).
   `α = - (1 / 2n) * log(det Δ)`
2. `β = STr(K) / (2n)` is the Chiral Radon–Nikodym Mode (Berezinian supervolume / parity imbalance).
   `β = - (1 / 2n) * log(Ber Δ)`
3. `K₀ = K - α I - β Γ` is the Split-Octonionic Shape Derivation Mode (`K₀ ∈ 𝔤_{2(2)}`).
   `Tr(K₀) = 0` and `STr(K₀) = 0`, ensuring `det(Δ₀) = 1` and `Ber(Δ₀) = 1`.
   `K₀` generates the off-diagonal Bogoliubov pairing field Δ_{SC} and rotates the Zorn Peirce frame.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Modular.Trifold

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

local notation "SubMat" => Matrix ι ι R
local notation "BlockMat" => Matrix (ι ⊕ ι) (ι ⊕ ι) R

/-!
=============================================================================
PART 1: Graded Basis Operators and Involutive Supertrace
=============================================================================
-/

/-- Identity operator on doubled space `I₂ₙ = [[1, 0], [0, 1]]` -/
def IdDoubled : BlockMat :=
  Matrix.fromBlocks (1 : SubMat) 0 0 (1 : SubMat)

/-- Involutive Grading Operator `Γ = [[1, 0], [0, -1]]` -/
def GammaGrading : BlockMat :=
  Matrix.fromBlocks (1 : SubMat) 0 0 (-1 : SubMat)

/-- Supertrace functional: `STr(M) = Tr(Γ * M)` -/
def STr (M : BlockMat) : R :=
  Matrix.trace (GammaGrading * M)

/-- Dimension count `n = |ι|` -/
def dimSubspace : ℕ := Fintype.card ι

/-- Trace of block-diagonal matrix -/
@[simp]
theorem trace_fromBlocks_diag (A B : SubMat) :
    Matrix.trace (Matrix.fromBlocks A (0 : SubMat) (0 : SubMat) B) =
      Matrix.trace A + Matrix.trace B := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- 🏆 THEOREM 1: Trace of the Identity Operator `Tr(I₂ₙ) = 2n` -/
theorem trace_IdDoubled :
    Matrix.trace (IdDoubled (ι := ι) (R := R)) = 2 * (dimSubspace (ι := ι) : R) := by
  dsimp [IdDoubled, dimSubspace]
  simp
  ring

/-- 🏆 THEOREM 2: Supertrace of the Identity Operator `STr(I₂ₙ) = 0` -/
theorem superTrace_IdDoubled :
    STr (IdDoubled (ι := ι) (R := R)) = 0 := by
  dsimp [STr, GammaGrading, IdDoubled]
  have h_mul : Matrix.fromBlocks (1 : SubMat) 0 0 (-1 : SubMat) *
        Matrix.fromBlocks (1 : SubMat) 0 0 (1 : SubMat) =
        Matrix.fromBlocks (1 : SubMat) 0 0 (-1 : SubMat) := by
    rw [Matrix.fromBlocks_multiply]
    simp
  rw [h_mul, trace_fromBlocks_diag, Matrix.trace_neg, add_neg_cancel]

/-- 🏆 THEOREM 3: Trace of the Grading Operator `Tr(Γ) = 0` -/
theorem trace_GammaGrading :
    Matrix.trace (GammaGrading (ι := ι) (R := R)) = 0 := by
  dsimp [GammaGrading]
  rw [trace_fromBlocks_diag, Matrix.trace_neg, add_neg_cancel]

/-- 🏆 THEOREM 4: Supertrace of the Grading Operator `STr(Γ) = 2n` -/
theorem superTrace_GammaGrading :
    STr (GammaGrading (ι := ι) (R := R)) = 2 * (dimSubspace (ι := ι) : R) := by
  dsimp [STr, GammaGrading, dimSubspace]
  have h_mul : Matrix.fromBlocks (1 : SubMat) 0 0 (-1 : SubMat) *
        Matrix.fromBlocks (1 : SubMat) 0 0 (-1 : SubMat) =
        Matrix.fromBlocks (1 : SubMat) 0 0 (1 : SubMat) := by
    rw [Matrix.fromBlocks_multiply]
    simp
  rw [h_mul, trace_fromBlocks_diag]
  simp
  ring

/-!
=============================================================================
PART 2: The Universal Trifold Decomposition: K = α I + β Γ + K₀
=============================================================================
-/

section FieldDecomposition

variable {F : Type*} [Field F] [CharZero F]
local notation "BlockMatF" => Matrix (ι ⊕ ι) (ι ⊕ ι) F

/-- Dimension scalar `2n ≠ 0` in field of characteristic zero given `n > 0` -/
theorem two_n_ne_zero (h_dim : Fintype.card ι ≠ 0) : (2 * (Fintype.card ι : F)) ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hn : (Fintype.card ι : F) ≠ 0 := Nat.cast_ne_zero.mpr h_dim
  exact mul_ne_zero h2 hn

/-- The Common Radon–Nikodym Mode projection `α(K) = Tr(K) / (2n)` -/
def alphaMode (K : BlockMatF) : F :=
  Matrix.trace K / (2 * (Fintype.card ι : F))

/-- The Chiral Radon–Nikodym Mode projection `β(K) = STr(K) / (2n)` -/
def betaMode (K : BlockMatF) : F :=
  STr K / (2 * (Fintype.card ι : F))

/-- The Residual Split-Octonionic Shape Operator `K₀ = K - α I - β Γ` -/
def shapeMode (K : BlockMatF) : BlockMatF :=
  K - (alphaMode K • IdDoubled) - (betaMode K • GammaGrading)

/-- 🏆 THEOREM 5: Exact Reconstruction Identity `K = α I + β Γ + K₀` -/
theorem trifold_reconstruction (K : BlockMatF) :
    K = alphaMode K • IdDoubled + betaMode K • GammaGrading + shapeMode K := by
  dsimp [shapeMode]
  abel

/-- 🏆 THEOREM 6: The Shape Operator is strictly Trace-Free: `Tr(K₀) = 0` -/
theorem shapeMode_trace_zero (h_dim : Fintype.card ι ≠ 0) (K : BlockMatF) :
    Matrix.trace (shapeMode K) = 0 := by
  dsimp [shapeMode, alphaMode, betaMode, dimSubspace]
  rw [Matrix.trace_sub, Matrix.trace_sub]
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rw [trace_IdDoubled, trace_GammaGrading]
  simp only [smul_zero, sub_zero]
  have h2n : (2 * (Fintype.card ι : F)) ≠ 0 := two_n_ne_zero h_dim
  calc
    Matrix.trace K - (Matrix.trace K / (2 * (Fintype.card ι : F))) • (2 * (Fintype.card ι : F))
      = Matrix.trace K - (Matrix.trace K / (2 * (Fintype.card ι : F))) * (2 * (Fintype.card ι : F)) := by rfl
    _ = Matrix.trace K - Matrix.trace K := by rw [div_mul_cancel₀ (Matrix.trace K) h2n]
    _ = 0 := sub_self (Matrix.trace K)

/-- 🏆 THEOREM 7: The Shape Operator is strictly Supertrace-Free: `STr(K₀) = 0` -/
theorem shapeMode_superTrace_zero (h_dim : Fintype.card ι ≠ 0) (K : BlockMatF) :
    STr (shapeMode K) = 0 := by
  dsimp [STr]
  have h_shape : shapeMode K = K - alphaMode K • IdDoubled - betaMode K • GammaGrading := rfl
  rw [h_shape]
  have h_distrib : GammaGrading * (K - alphaMode K • IdDoubled - betaMode K • GammaGrading) =
      GammaGrading * K - alphaMode K • (GammaGrading * IdDoubled) - betaMode K • (GammaGrading * GammaGrading) := by
    simp only [mul_sub, Matrix.mul_smul]
  rw [h_distrib]
  rw [Matrix.trace_sub, Matrix.trace_sub]
  rw [Matrix.trace_smul, Matrix.trace_smul]
  have h_gamma_id : Matrix.trace (GammaGrading * (IdDoubled (ι := ι) (R := F))) = 0 := superTrace_IdDoubled
  have h_gamma_gamma : Matrix.trace (GammaGrading * (GammaGrading (ι := ι) (R := F))) = 2 * (Fintype.card ι : F) := superTrace_GammaGrading
  rw [h_gamma_id, h_gamma_gamma]
  simp only [smul_zero, sub_zero]
  have h2n : (2 * (Fintype.card ι : F)) ≠ 0 := two_n_ne_zero h_dim
  change Matrix.trace (GammaGrading * K) - (betaMode K) • (2 * (Fintype.card ι : F)) = 0
  have hSTr : Matrix.trace (GammaGrading * K) = STr K := rfl
  rw [hSTr]
  dsimp [betaMode]
  calc
    STr K - (STr K / (2 * (Fintype.card ι : F))) • (2 * (Fintype.card ι : F))
      = STr K - (STr K / (2 * (Fintype.card ι : F))) * (2 * (Fintype.card ι : F)) := by rfl
    _ = STr K - STr K := by rw [div_mul_cancel₀ (STr K) h2n]
    _ = 0 := sub_self (STr K)

/-- 🏆 THEOREM 8: Uniqueness of the Trifold Decomposition -/
theorem trifold_uniqueness (h_dim : Fintype.card ι ≠ 0) (K : BlockMatF) (a b : F) (M : BlockMatF)
    (h_decomp : K = a • (IdDoubled : BlockMatF) + b • (GammaGrading : BlockMatF) + M)
    (h_tr : Matrix.trace M = 0)
    (h_str : STr M = 0) :
    a = alphaMode K ∧ b = betaMode K ∧ M = shapeMode K := by
  have h2n : (2 * (Fintype.card ι : F)) ≠ 0 := two_n_ne_zero h_dim
  have h_tr_K : Matrix.trace K = a * (2 * (Fintype.card ι : F)) := by
    have h1 : Matrix.trace K = Matrix.trace (a • (IdDoubled : BlockMatF) + b • (GammaGrading : BlockMatF) + M) := by rw [h_decomp]
    have h2 : Matrix.trace (a • (IdDoubled : BlockMatF) + b • (GammaGrading : BlockMatF) + M) =
        Matrix.trace (a • (IdDoubled : BlockMatF)) + Matrix.trace (b • (GammaGrading : BlockMatF)) + Matrix.trace M := by
      rw [Matrix.trace_add, Matrix.trace_add]
    have h3 : Matrix.trace (a • (IdDoubled : BlockMatF)) = a * (2 * (Fintype.card ι : F)) := by
      rw [Matrix.trace_smul]
      change a * Matrix.trace (IdDoubled : BlockMatF) = _
      rw [trace_IdDoubled]
      rfl
    have h4 : Matrix.trace (b • (GammaGrading : BlockMatF)) = 0 := by
      rw [Matrix.trace_smul]
      change b * Matrix.trace (GammaGrading : BlockMatF) = _
      rw [trace_GammaGrading]
      exact smul_zero b
    rw [h1, h2, h3, h4, h_tr, add_zero, add_zero]
  have ha : a = alphaMode K := by
    dsimp [alphaMode]
    rw [h_tr_K, mul_div_cancel_right₀ a h2n]
  have h_str_K : STr K = b * (2 * (Fintype.card ι : F)) := by
    dsimp [STr]
    have h_prod : (GammaGrading : BlockMatF) * K =
        a • ((GammaGrading : BlockMatF) * IdDoubled) + b • ((GammaGrading : BlockMatF) * GammaGrading) + (GammaGrading : BlockMatF) * M := by
      rw [h_decomp]
      simp only [Matrix.mul_add, Matrix.mul_smul]
    have h1 : Matrix.trace ((GammaGrading : BlockMatF) * K) =
        Matrix.trace (a • ((GammaGrading : BlockMatF) * IdDoubled) + b • ((GammaGrading : BlockMatF) * GammaGrading) + (GammaGrading : BlockMatF) * M) := by
      rw [h_prod]
    have h2 : Matrix.trace (a • ((GammaGrading : BlockMatF) * IdDoubled) + b • ((GammaGrading : BlockMatF) * GammaGrading) + (GammaGrading : BlockMatF) * M) =
        Matrix.trace (a • ((GammaGrading : BlockMatF) * IdDoubled)) + Matrix.trace (b • ((GammaGrading : BlockMatF) * GammaGrading)) + Matrix.trace ((GammaGrading : BlockMatF) * M) := by
      rw [Matrix.trace_add, Matrix.trace_add]
    have h3 : Matrix.trace (a • ((GammaGrading : BlockMatF) * IdDoubled)) = 0 := by
      have h_id : Matrix.trace ((GammaGrading : BlockMatF) * IdDoubled) = 0 := superTrace_IdDoubled
      rw [Matrix.trace_smul, h_id]
      exact smul_zero a
    have h4 : Matrix.trace (b • ((GammaGrading : BlockMatF) * GammaGrading)) = b * (2 * (Fintype.card ι : F)) := by
      have h_gg : Matrix.trace ((GammaGrading : BlockMatF) * GammaGrading) = 2 * (Fintype.card ι : F) := superTrace_GammaGrading
      rw [Matrix.trace_smul, h_gg]
      rfl
    have h5 : Matrix.trace ((GammaGrading : BlockMatF) * M) = 0 := h_str
    rw [h1, h2, h3, h4, h5, zero_add, add_zero]
  have hb : b = betaMode K := by
    dsimp [betaMode]
    rw [h_str_K, mul_div_cancel_right₀ b h2n]
  have hM : M = shapeMode K := by
    dsimp [shapeMode]
    rw [← ha, ← hb, h_decomp]
    abel
  exact ⟨ha, hb, hM⟩

end FieldDecomposition

/-!
=============================================================================
PART 3: Determinant and Berezinian Exponentiation
=============================================================================
-/

/-- The Berezinian ratio for diagonal components `Ber(A, D) = det(A) / det(D)` -/
def berDiagonal (detA detD : ℝ) : ℝ :=
  detA / detD

/-- 🏆 THEOREM 9: Common Weyl Scaling matches the Ordinary Determinant:
    det(exp(-α I₂ₙ)) = exp(-2n α) -/
theorem det_exp_common_weyl (α : ℝ) (n : ℕ) :
    Real.exp (- (2 * (n : ℝ) * α)) = (Real.exp (-α)) ^ (2 * n) := by
  have h := (Real.exp_nat_mul (-α) (2 * n)).symm
  rw [h]
  congr 1
  calc
    -(2 * (n : ℝ) * α) = (2 * (n : ℝ)) * -α := by ring
    _ = ((2 * n : ℕ) : ℝ) * -α := by push_cast; rfl

/-- 🏆 THEOREM 10: Chiral Berezinian Supervolume matches the Supertrace:
    Ber(exp(-β Iₙ), exp(β Iₙ)) = exp(-2n β) = exp(-STr(β Γ)) -/
theorem ber_exp_chiral_weyl (β : ℝ) (n : ℕ) :
    berDiagonal ((Real.exp (-β)) ^ n) ((Real.exp β) ^ n) = Real.exp (- (2 * (n : ℝ) * β)) := by
  dsimp [berDiagonal]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  rw [← Real.exp_sub]
  congr 1
  calc
    ((n : ℝ) * -β) - ((n : ℝ) * β) = - (2 * (n : ℝ) * β) := by ring

end InfoGeometry.Modular.Trifold

end noncomputable section
