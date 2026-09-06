import Mathlib
import proofs.SplitOctonionAlgebra
import proofs.SplitOctonionNorm44
import proofs.SplitOctonionTrialityCore
import proofs.SplitOctonionLeftRightMultiplication
import proofs.SplitOctonionAlternativityHelpers

open SplitOctonion
open SplitOctonionNorm44
open SplitOctonionTrialityCore

-- Given D ∈ Der(O), α, β ∈ Im(O), we construct A, B, C.
def norm_A (D : SplitOct →ₗ[ℝ] SplitOct) (α β : SplitOct) : SplitOct →ₗ[ℝ] SplitOct :=
  D + lmul α + rmul β

def norm_B (D : SplitOct →ₗ[ℝ] SplitOct) (α β : SplitOct) : SplitOct →ₗ[ℝ] SplitOct :=
  D + lmul α + rmul (α - β)

def norm_C (D : SplitOct →ₗ[ℝ] SplitOct) (α β : SplitOct) : SplitOct →ₗ[ℝ] SplitOct :=
  D - lmul (α - β) + rmul β

lemma isTriality_of_deriv_lmul_rmul (D : SplitOct →ₗ[ℝ] SplitOct) (hD : ∀ x y, D (x * y) = D x * y + x * D y)
  (α β : SplitOct) :
  ∀ x y : SplitOct,
    norm_A D α β (x * y) = norm_B D α β x * y + x * norm_C D α β y := by
  intro x y
  
  have h1 : norm_A D α β (x * y) = D (x * y) + α * (x * y) + (x * y) * β := rfl
  have h2 : norm_B D α β x * y = (D x + α * x + x * (α - β)) * y := rfl
  have h3 : x * norm_C D α β y = x * (D y - (α - β) * y + y * β) := rfl
  
  rw [h1, h2, h3, hD]
  have hl := left_linearized_alternative' α x y
  have hr := right_linearized_alternative' x y β
  rw [hl, hr]
  simp only [add_mul, sub_mul, mul_add, mul_sub]
  abel
