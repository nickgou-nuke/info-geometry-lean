import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.QuantumGeometry.Projective

open scoped InnerProductSpace
open ContinuousLinearMap

abbrev EndH (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Type _ :=
  H →L[ℂ] H

def IsSkewAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : EndH H) : Prop :=
  adjoint A = -A

namespace IsSkewAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A B : EndH H}

theorem add (hA : IsSkewAdjoint A) (hB : IsSkewAdjoint B) : IsSkewAdjoint (A + B) := by
  dsimp [IsSkewAdjoint] at *
  rw [map_add, hA, hB, neg_add]

theorem smul (r : ℝ) (hA : IsSkewAdjoint A) : IsSkewAdjoint (r • A) := by
  dsimp [IsSkewAdjoint] at *
  have h : adjoint (r • A) = (starRingEnd ℂ (r : ℂ)) • adjoint A := by
    exact map_smulₛₗ adjoint (r : ℂ) A
  rw [Complex.conj_ofReal] at h
  rw [h, hA, smul_neg]
  rfl

theorem lie (hA : IsSkewAdjoint A) (hB : IsSkewAdjoint B) : IsSkewAdjoint (A * B - B * A) := by
  dsimp [IsSkewAdjoint] at *
  have h_comp1 : adjoint (A * B) = adjoint B * adjoint A := adjoint_comp A B
  have h_comp2 : adjoint (B * A) = adjoint A * adjoint B := adjoint_comp B A
  rw [map_sub, h_comp1, h_comp2, hA, hB, neg_mul_neg, neg_mul_neg, neg_sub]

end IsSkewAdjoint

def skewAdjointSubmodule (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Submodule ℝ (EndH H) where
  carrier := {A | IsSkewAdjoint A}
  add_mem' {A B} hA hB := IsSkewAdjoint.add hA hB
  zero_mem' := by
    dsimp [IsSkewAdjoint]
    rw [map_zero, neg_zero]
  smul_mem' c A hA := IsSkewAdjoint.smul c hA

abbrev SkewAdjoint (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  skewAdjointSubmodule H

def skewBracket {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : SkewAdjoint H) : SkewAdjoint H :=
  ⟨A.1 * B.1 - B.1 * A.1, IsSkewAdjoint.lie A.2 B.2⟩

instance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    LieRing (SkewAdjoint H) where
  bracket := skewBracket
  add_lie := by intro A B C; ext; simp only [Submodule.coe_add, skewBracket]; noncomm_ring
  lie_add := by intro A B C; ext; simp only [Submodule.coe_add, skewBracket]; noncomm_ring
  lie_self := by intro A; ext; simp only [skewBracket, sub_self, Submodule.coe_zero]
  leibniz_lie := by
    intro A B C
    ext
    simp only [skewBracket, Submodule.coe_add]
    noncomm_ring

instance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    LieAlgebra ℝ (SkewAdjoint H) where
  lie_smul := by
    intro r A B
    apply Subtype.ext
    show A.1 * (r • B.1) - (r • B.1) * A.1 = r • (A.1 * B.1 - B.1 * A.1)
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

namespace SkewAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical Lie homomorphism from `SkewAdjoint H` into `EndH H`. -/
noncomputable def toLieHom : SkewAdjoint H →ₗ⁅ℝ⁆ EndH H :=
  { toFun := Subtype.val
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    map_lie' := fun {_ _} => by
      dsimp [Ring.lie_def, skewBracket]
      rfl }

theorem toLieHom_injective : Function.Injective (toLieHom (H := H)) :=
  Subtype.val_injective

end SkewAdjoint

structure ProjectiveQGT (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  metric : LinearMap.BilinForm ℝ (EndH H)
  berry : LinearMap.BilinForm ℝ (EndH H)
  metric_symm : metric.IsSymm
  berry_alt : berry.IsAlt
  complexAction (A : EndH H) : EndH H := Complex.I • A
  compat : ∀ A B, berry A B = metric A (complexAction B)

namespace ProjectiveQGT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def ofState (ψ : H) (_hψ : ψ ≠ 0) : ProjectiveQGT H where
  metric := LinearMap.mk₂ ℝ
    (fun A B => (⟪A ψ, B ψ⟫_ℂ).re / (‖ψ‖ ^ 2))
    (by intro A₁ A₂ B; simp [ContinuousLinearMap.add_apply, inner_add_left, add_div])
    (by
      intro c A B
      simp only [ContinuousLinearMap.smul_apply, inner_smul_left_eq_smul, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_div_assoc]
      rfl)
    (by intro A B₁ B₂; simp [ContinuousLinearMap.add_apply, inner_add_right, add_div])
    (by
      intro c A B
      simp only [ContinuousLinearMap.smul_apply, inner_smul_right_eq_smul, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_div_assoc]
      rfl)
  berry := LinearMap.mk₂ ℝ
    (fun A B => -(⟪A ψ, B ψ⟫_ℂ).im / (‖ψ‖ ^ 2))
    (by intro A₁ A₂ B; simp [ContinuousLinearMap.add_apply, inner_add_left]; ring)
    (by
      intro c A B
      simp only [ContinuousLinearMap.smul_apply, inner_smul_left_eq_smul, Complex.real_smul,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, smul_eq_mul]
      ring)
    (by intro A B₁ B₂; simp [ContinuousLinearMap.add_apply, inner_add_right]; ring)
    (by
      intro c A B
      simp only [ContinuousLinearMap.smul_apply, inner_smul_right_eq_smul, Complex.real_smul,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, smul_eq_mul]
      ring)
  metric_symm := ⟨fun A B => by
    dsimp
    rw [← inner_conj_symm (A ψ) (B ψ), Complex.conj_re]⟩
  berry_alt := fun A => by
    dsimp
    have h : (⟪A ψ, A ψ⟫_ℂ).im = 0 := @inner_self_im ℂ H _ _ _ (A ψ)
    rw [h, neg_zero, zero_div]
  compat := by
    intro A B
    dsimp [complexAction]
    rw [inner_smul_right, Complex.I_mul_re]

theorem ofState_metric_apply (ψ : H) (hψ : ψ ≠ 0) (A B : EndH H) :
    (ofState ψ hψ).metric A B = (⟪A ψ, B ψ⟫_ℂ).re / (‖ψ‖ ^ 2) := rfl

theorem ofState_berry_apply (ψ : H) (hψ : ψ ≠ 0) (A B : EndH H) :
    (ofState ψ hψ).berry A B = -(⟪A ψ, B ψ⟫_ℂ).im / (‖ψ‖ ^ 2) := rfl

theorem ofState_metric_self_nonneg (ψ : H) (hψ : ψ ≠ 0) (A : EndH H) :
    0 ≤ (ofState ψ hψ).metric A A := by
  dsimp [ofState_metric_apply]
  apply div_nonneg
  · exact @inner_self_nonneg ℂ H _ _ _ (A ψ)
  · positivity

end ProjectiveQGT

end InfoGeometry.QuantumGeometry.Projective
