import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Neutral (4,4) Krein Space and Cartan Reduction to Positive Hilbert Operators

This module formalizes:
1. The neutral (4,4) signature fundamental symmetry matrix J₄₄ = diag(I₄, -I₄) on ℂ⁸.
2. Verification that J₄₄ is self-adjoint (J₄₄† = J₄₄) and involutive (J₄₄² = I₈).
3. The Krein adjoint on 8×8 complex matrices: M♯ = J₄₄ * M† * J₄₄.
4. The Krein-skew condition M♯ = -M characterizing the real Lie algebra 𝔬(4,4).
5. Block matrix structure:
     M = [ X   Y ]
         [ Y†  Z ]
   where X = -X† (skew-adjoint on ℂ⁴), Z = -Z† (skew-adjoint on ℂ⁴), and Y is arbitrary.
6. The Cartan involution θ(M) = J₄₄ * M * J₄₄ = - M† on Krein-skew operators.
7. Exact Cartan decomposition into:
   - Compact Hilbert skew-adjoint part: M_𝔨 = (1/2)(M + θ(M)) satisfying (M_𝔨)† = - M_𝔨
   - Non-compact Hilbert self-adjoint part: M_𝔭 = (1/2)(M - θ(M)) satisfying (M_𝔭)† = M_𝔭

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open Matrix

namespace InfoGeometry.Lie.NeutralKrein

abbrev Dim4 := Fin 4
abbrev Dim8 := Fin 4 ⊕ Fin 4

local notation "Mat4" => Matrix Dim4 Dim4 ℂ
local notation "Mat8" => Matrix Dim8 Dim8 ℂ

/-- The (4,4) fundamental symmetry matrix J₄₄ = diag(I₄, -I₄). -/
def J44 : Mat8 :=
  fromBlocks (1 : Mat4) 0 0 (- (1 : Mat4))

@[simp]
theorem J44_conjTranspose : J44ᴴ = J44 := by
  dsimp [J44]
  rw [fromBlocks_conjTranspose]
  simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg]

@[simp]
theorem J44_mul_self : J44 * J44 = (1 : Mat8) := by
  dsimp [J44]
  rw [fromBlocks_multiply]
  simp only [mul_one, mul_zero, add_zero, zero_add,
             mul_neg, neg_neg, neg_zero]
  exact fromBlocks_one

/-- The Krein adjoint on 8×8 matrices: M♯ = J₄₄ * Mᴴ * J₄₄. -/
def kreinAdjoint (M : Mat8) : Mat8 :=
  J44 * Mᴴ * J44

/-- A matrix is Krein-skew if M♯ = -M. -/
def IsKreinSkew (M : Mat8) : Prop :=
  kreinAdjoint M = - M

/-- The Cartan involution on 8×8 matrices: θ(M) = J₄₄ * M * J₄₄. -/
def cartanInvolution (M : Mat8) : Mat8 :=
  J44 * M * J44

/-- On Krein-skew matrices, the Cartan involution is - Mᴴ. -/
theorem cartanInvolution_of_isKreinSkew (M : Mat8) (hM : IsKreinSkew M) :
    cartanInvolution M = - Mᴴ := by
  dsimp [IsKreinSkew, kreinAdjoint] at hM
  have h_wrap : J44 * (J44 * Mᴴ * J44) * J44 = J44 * (-M) * J44 := by
    rw [hM]
  have h_lhs : J44 * (J44 * Mᴴ * J44) * J44 = Mᴴ := by
    calc
      J44 * (J44 * Mᴴ * J44) * J44 = (J44 * J44) * Mᴴ * (J44 * J44) := by
        simp only [Matrix.mul_assoc]
      _ = (1 : Mat8) * Mᴴ * (1 : Mat8) := by rw [J44_mul_self]
      _ = Mᴴ := by simp only [Matrix.one_mul, Matrix.mul_one]
  have h_rhs : J44 * (-M) * J44 = - (J44 * M * J44) := by
    simp only [Matrix.mul_neg, Matrix.neg_mul]
  rw [h_lhs, h_rhs] at h_wrap
  dsimp [cartanInvolution]
  exact neg_eq_iff_eq_neg.mp h_wrap.symm

/-- The compact part of a matrix: M_𝔨 = (1/2) • (M + θ(M)). -/
def compactPart (M : Mat8) : Mat8 :=
  (1 / 2 : ℂ) • (M + cartanInvolution M)

/-- The non-compact part of a matrix: M_𝔭 = (1/2) • (M - θ(M)). -/
def noncompactPart (M : Mat8) : Mat8 :=
  (1 / 2 : ℂ) • (M - cartanInvolution M)

/-- Exact reconstruction: M = M_𝔨 + M_𝔭. -/
theorem cartan_reconstruction (M : Mat8) :
    compactPart M + noncompactPart M = M := by
  dsimp [compactPart, noncompactPart]
  rw [← smul_add]
  have h_add : (M + cartanInvolution M) + (M - cartanInvolution M) = (2 : ℂ) • M := by
    calc
      (M + cartanInvolution M) + (M - cartanInvolution M)
        = (M + M) + (cartanInvolution M - cartanInvolution M) := by abel
      _ = (2 : ℂ) • M + 0 := by rw [two_smul, sub_self]
      _ = (2 : ℂ) • M := by rw [add_zero]
  rw [h_add, smul_smul]
  have h_half : (1 / 2 : ℂ) * 2 = 1 := by ring
  rw [h_half, one_smul]

/-- THEOREM 1: The compact part M_𝔨 is strictly Hilbert skew-adjoint: (M_𝔨)† = - M_𝔨. -/
theorem compactPart_is_hilbert_skew (M : Mat8) (hM : IsKreinSkew M) :
    (compactPart M)ᴴ = - compactPart M := by
  dsimp [compactPart]
  rw [conjTranspose_smul, conjTranspose_add]
  have h_half : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    apply Complex.ext <;> simp
  rw [h_half]
  have h_adjM : Mᴴ = - cartanInvolution M := by
    have h_inv := cartanInvolution_of_isKreinSkew M hM
    exact neg_eq_iff_eq_neg.mp h_inv.symm
  have h_adj_theta : (cartanInvolution M)ᴴ = - M := by
    dsimp [cartanInvolution]
    calc
      (J44 * M * J44)ᴴ = J44ᴴ * Mᴴ * J44ᴴ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J44 * Mᴴ * J44 := by rw [J44_conjTranspose]
      _ = kreinAdjoint M := rfl
      _ = -M := hM
  rw [h_adjM, h_adj_theta]
  have h_sum : - cartanInvolution M + - M = - (M + cartanInvolution M) := by abel
  rw [h_sum, smul_neg]

/-- THEOREM 2: The non-compact part M_𝔭 is strictly Hilbert self-adjoint: (M_𝔭)† = M_𝔭. -/
theorem noncompactPart_is_hilbert_self_adjoint (M : Mat8) (hM : IsKreinSkew M) :
    (noncompactPart M)ᴴ = noncompactPart M := by
  dsimp [noncompactPart]
  rw [conjTranspose_smul, conjTranspose_sub]
  have h_half : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    apply Complex.ext <;> simp
  rw [h_half]
  have h_adjM : Mᴴ = - cartanInvolution M := by
    have h_inv := cartanInvolution_of_isKreinSkew M hM
    exact neg_eq_iff_eq_neg.mp h_inv.symm
  have h_adj_theta : (cartanInvolution M)ᴴ = - M := by
    dsimp [cartanInvolution]
    calc
      (J44 * M * J44)ᴴ = J44ᴴ * Mᴴ * J44ᴴ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = J44 * Mᴴ * J44 := by rw [J44_conjTranspose]
      _ = kreinAdjoint M := rfl
      _ = -M := hM
  rw [h_adjM, h_adj_theta]
  have h_sub : - cartanInvolution M - - M = M - cartanInvolution M := by abel
  rw [h_sub]

/-- 
  THEOREM 3 (Block Structure of 𝔬(4,4) Krein Derivations):
  For any block matrix M = fromBlocks X Y Z W, M is Krein-skew if and only if
  X is skew-adjoint (Xᴴ = -X), W is skew-adjoint (Wᴴ = -W), and Z = Yᴴ.
-/
theorem isKreinSkew_fromBlocks_iff (X Y Z W : Mat4) :
    IsKreinSkew (fromBlocks X Y Z W) ↔
      (Xᴴ = - X ∧ Wᴴ = - W ∧ Z = Yᴴ) := by
  dsimp [IsKreinSkew, kreinAdjoint, J44]
  rw [fromBlocks_conjTranspose]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
             mul_neg, neg_mul, neg_neg]
  rw [fromBlocks_neg, fromBlocks_inj]
  constructor
  · rintro ⟨hX, hY, hZ, hW⟩
    have hZ_eq : Z = Yᴴ := by
      have h : - Zᴴ = - Y := hY
      have h1 : Zᴴ = Y := neg_inj.mp h
      have h2 := congr_arg conjTranspose h1
      rw [conjTranspose_conjTranspose] at h2
      exact h2
    exact ⟨hX, hW, hZ_eq⟩
  · rintro ⟨hX, hW, rfl⟩
    refine ⟨hX, ?_, ?_, hW⟩
    · simp
    · simp

end InfoGeometry.Lie.NeutralKrein

end noncomputable section
