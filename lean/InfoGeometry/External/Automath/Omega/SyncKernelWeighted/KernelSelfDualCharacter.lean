import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import InfoGeometry.External.Automath.Omega.SyncKernelWeighted.KernelSelfDualCharacterSchur

namespace Omega.SyncKernelWeighted

open Matrix

noncomputable section

/-- The chapter-local character-twisted transfer matrix `Bχ(u) = B₀ + u χ(g₁) B₁`. -/
def kernelCharacterTwist {n : Type*} [Fintype n] [DecidableEq n] (u chi : ℂ)
    (B₀ B₁ : Matrix n n ℂ) : Matrix n n ℂ :=
  B₀ + (u * chi) • B₁

/-- Determinant package attached to the character-twisted transfer matrix. -/
def kernelCharacterDet {n : Type*} [Fintype n] [DecidableEq n] (z u chi : ℂ)
    (B₀ B₁ : Matrix n n ℂ) : ℂ :=
  Matrix.det (1 - z • kernelCharacterTwist u chi B₀ B₁)

/-- Zeta package attached to the character-twisted transfer matrix. -/
def kernelCharacterZeta {n : Type*} [Fintype n] [DecidableEq n] (z u chi : ℂ)
    (B₀ B₁ : Matrix n n ℂ) : ℂ :=
  (kernelCharacterDet z u chi B₀ B₁)⁻¹

/-- Conjugating `Bχ(u)` by the self-duality involution exchanges `B₀` and `B₁`, yielding the
character-level functional equation and its determinant/zeta corollaries.
    prop:kernel-self-dual-character -/
theorem paper_kernel_self_dual_character {n : Type*} [Fintype n] [DecidableEq n] (u chi z : ℂ)
    (B₀ B₁ P : Matrix n n ℂ) (hP : IsUnit P.det) (hu : u ≠ 0) (hchi : chi ≠ 0)
    (hB₀ : P⁻¹ * B₀ * P = B₁) (hB₁ : P⁻¹ * B₁ * P = B₀) :
    P⁻¹ * kernelCharacterTwist u chi B₀ B₁ * P =
        (u * chi) • kernelCharacterTwist u⁻¹ chi⁻¹ B₀ B₁ ∧
      kernelCharacterDet z u chi B₀ B₁ =
        kernelCharacterDet ((u * chi) * z) u⁻¹ chi⁻¹ B₀ B₁ ∧
      kernelCharacterZeta z u chi B₀ B₁ =
        kernelCharacterZeta ((u * chi) * z) u⁻¹ chi⁻¹ B₀ B₁ := by
  have hsim :
      P⁻¹ * kernelCharacterTwist u chi B₀ B₁ * P =
        (u * chi) • kernelCharacterTwist u⁻¹ chi⁻¹ B₀ B₁ := by
    have hscalar : (u * chi) * (u⁻¹ * chi⁻¹) = 1 := by
      field_simp [hu, hchi, mul_assoc, mul_left_comm, mul_comm]
    calc
      P⁻¹ * kernelCharacterTwist u chi B₀ B₁ * P
          = P⁻¹ * B₀ * P + (u * chi) • (P⁻¹ * B₁ * P) := by
              simp [kernelCharacterTwist, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = B₁ + (u * chi) • B₀ := by rw [hB₀, hB₁]
      _ = (u * chi) • kernelCharacterTwist u⁻¹ chi⁻¹ B₀ B₁ := by
            simp [kernelCharacterTwist, smul_add, smul_smul, hscalar, add_comm]
  have hsimLaw :
      schurSimilarityLaw 1 u chi (kernelCharacterTwist u chi B₀ B₁)
        (kernelCharacterTwist u⁻¹ chi⁻¹ B₀ B₁) P := by
    simpa [schurSimilarityLaw] using hsim
  have hdet :
      kernelCharacterDet z u chi B₀ B₁ =
        kernelCharacterDet ((u * chi) * z) u⁻¹ chi⁻¹ B₀ B₁ := by
    simpa [kernelCharacterDet, schurDeterminantFunctionalEquation] using
      (paper_kernel_self_dual_character_schur (n := n) (q := 1) u chi z
        (kernelCharacterTwist u chi B₀ B₁) (kernelCharacterTwist u⁻¹ chi⁻¹ B₀ B₁) P hP
        hsimLaw).2
  refine ⟨hsim, hdet, ?_⟩
  unfold kernelCharacterZeta
  rw [hdet]

end

end Omega.SyncKernelWeighted
