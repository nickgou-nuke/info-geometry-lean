import Mathlib.Algebra.Module.LinearMap.End
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Tactic.Abel

set_option linter.unusedVariables false

/-!
# Cartan Involution Foundation (Strictly Algebraic)

This module implements the algebraic foundation for gradings using Cartan 
involutions in the endomorphism ring `Module.End 𝕜 E`. 

Hierarchy:
1. A Cartan involution θ is an endomorphism squaring to identity.
2. It generates canonical projectors P₊ and P₋.
3. These projectors define the space grading and operator parity.

All proofs are purely algebraic in the endomorphism ring, avoiding point-wise 
evaluation on vectors to ensure maximum performance and universe consistency.
-/

namespace InfoGeometry.Cartan

variable {𝕜 E : Type*} [Field 𝕜] [Invertible (2 : 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]

/-- A Cartan involution is an endomorphism that squares to the identity. -/
def IsCartanInvolution (θ : Module.End 𝕜 E) : Prop :=
  θ * θ = 1

variable (θ : Module.End 𝕜 E)

/-- Projection to the +1 eigenspace: P₊ = 1/2 (id + θ). -/
noncomputable def Pplus : Module.End 𝕜 E :=
  (⅟(2 : 𝕜)) • (1 + θ)

/-- Projection to the -1 eigenspace: P₋ = 1/2 (id - θ). -/
noncomputable def Pminus : Module.End 𝕜 E :=
  (⅟(2 : 𝕜)) • (1 - θ)

/-! ### Strictly Algebraic Identities (Endomorphism Ring) -/

/-- Pplus is idempotent: P₊ * P₊ = P₊. -/
lemma Pplus_idempotent (hθ : IsCartanInvolution θ) : (Pplus θ) * (Pplus θ) = Pplus θ := by
  dsimp [Pplus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_expand : (1 + θ) * (1 + θ) = (2 : 𝕜) • (1 + θ) := by
    calc
      (1 + θ) * (1 + θ) = 1 + θ + θ + θ * θ := by
        rw [add_mul, one_mul, mul_add, mul_one, ← add_assoc]
      _ = 1 + θ + θ + 1 := by
        rw [hθ]
      _ = (1 + 1) + (θ + θ) := by
        abel_nf
      _ = (2 : 𝕜) • 1 + (2 : 𝕜) • θ := by
        rw [two_smul, two_smul]
      _ = (2 : 𝕜) • (1 + θ) := by
        rw [smul_add]
  rw [h_expand, smul_smul, mul_assoc, invOf_mul_self, mul_one]

/-- Pminus is idempotent: P₋ * P₋ = P₋. -/
lemma Pminus_idempotent (hθ : IsCartanInvolution θ) : (Pminus θ) * (Pminus θ) = Pminus θ := by
  dsimp [Pminus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_expand : (1 - θ) * (1 - θ) = (2 : 𝕜) • (1 - θ) := by
    calc
      (1 - θ) * (1 - θ) = 1 - θ - θ + θ * θ := by
        rw [sub_mul, one_mul, mul_sub, mul_one]
        abel_nf
      _ = 1 - θ - θ + 1 := by
        rw [hθ]
      _ = (1 + 1) - (θ + θ) := by
        abel_nf
      _ = (2 : 𝕜) • 1 - (2 : 𝕜) • θ := by
        rw [two_smul, two_smul]
      _ = (2 : 𝕜) • (1 - θ) := by
        rw [smul_sub]
  rw [h_expand, smul_smul, mul_assoc, invOf_mul_self, mul_one]

/-- The sum of the projectors is the identity. -/
lemma Pplus_add_Pminus_eq_id : Pplus θ + Pminus θ = 1 := by
  dsimp [Pplus, Pminus]
  rw [← smul_add]
  have h_sum : (1 + θ) + (1 - θ) = (2 : 𝕜) • 1 := by
    calc
      (1 + θ) + (1 - θ) = (1 + 1) := by
        abel_nf
      _ = (2 : 𝕜) • 1 := by
        rw [two_smul]
  rw [h_sum, smul_smul, invOf_mul_self, one_smul]

/-- Projectors are complementary: P₊ * P₋ = 0. -/
lemma Pplus_comp_Pminus (hθ : IsCartanInvolution θ) : (Pplus θ) * (Pminus θ) = 0 := by
  dsimp [Pplus, Pminus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_expand : (1 + θ) * (1 - θ) = 1 - θ * θ := by
    rw [add_mul, one_mul, mul_sub, mul_one]
    abel_nf
  rw [h_expand, hθ, sub_self, smul_zero]

/-- Projectors are complementary in the opposite order: P₋ * P₊ = 0. -/
lemma Pminus_comp_Pplus (hθ : IsCartanInvolution θ) : (Pminus θ) * (Pplus θ) = 0 := by
  dsimp [Pplus, Pminus]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h_expand : (1 - θ) * (1 + θ) = 1 - θ * θ := by
    rw [sub_mul, one_mul, mul_add, mul_one]
    abel_nf
  rw [h_expand, hθ, sub_self, smul_zero]

/-! ### Vector Bridge Lemmas (Pointwise Descent) -/

lemma Pplus_apply (x : E) : (Pplus θ) x = (⅟(2 : 𝕜)) • (x + θ x) := by
  simp only [Pplus, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply]

lemma Pminus_apply (x : E) : (Pminus θ) x = (⅟(2 : 𝕜)) • (x - θ x) := by
  simp only [Pminus, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]

lemma decompose (hθ : IsCartanInvolution θ) (x : E) : x = (Pplus θ) x + (Pminus θ) x := by
  rw [← LinearMap.add_apply, Pplus_add_Pminus_eq_id, Module.End.one_apply]

end InfoGeometry.Cartan
