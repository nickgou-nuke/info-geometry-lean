import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

/-!
# Quantum Geometric Tensor — Projective (Complex) Formulation

This module formalizes the Quantum Geometric Tensor (QGT) on the projective
Hilbert space of a complex Hilbert space `H`.  The tensor is built from the
real and imaginary parts of the Hilbert–Schmidt pairing on the bounded
operator algebra `End H`:

  * `g(A, B) = Re ⟨A, B⟩_ℂ`
  * `Ω(A, B) = -Im ⟨A, B⟩_ℂ`

and satisfies the Kähler compatibility `Ω(A, B) = g(A, J B)` with complex
structure `J(A) = Complex.I • A`.

We also formalize the real Lie algebra `𝔰𝔲(H)` of skew-adjoint operators and
the canonical Lie-homomorphism `SkewAdjointLieRep` into `End H`.
-/

namespace InfoGeometry.QuantumGeometry.Projective

open scoped InnerProductSpace

/-- Bounded operators on `H`. -/
abbrev EndH (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Type _ :=
  H →L[ℂ] H

/-- `A` is **skew-adjoint** iff `A† = -A`. -/
def IsSkewAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : EndH H) : Prop :=
  ContinuousLinearMap.adjoint A = -A

namespace IsSkewAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A B : EndH H}

theorem adjoint_eq (h : IsSkewAdjoint A) : ContinuousLinearMap.adjoint A = -A := h

  theorem neg_adjoint (h : IsSkewAdjoint A) : IsSkewAdjoint (-A) := by
    ext x
    ext y
    have : ⟪x, A y⟫ = -⟪A x, y⟫ := by
      rw [← adjoint_inner_right, h, inner_neg_right]
    simp [this, inner_neg_left, inner_neg_right, neg_neg]

  theorem add (hA : IsSkewAdjoint A) (hB : IsSkewAdjoint B) : IsSkewAdjoint (A + B) := by
    ext x y
    have h₁ : ⟪A x, y⟫ = -⟪x, A y⟫ := by
      rw [← adjoint_inner_right, hA, inner_neg_right]
    have h₂ : ⟪B x, y⟫ = -⟪x, B y⟫ := by
      rw [← adjoint_inner_right, hB, inner_neg_right]
    simp [h₁, h₂, inner_add_left, inner_add_right, add_comm]

  theorem smul (r : ℝ) (hA : IsSkewAdjoint A) : IsSkewAdjoint ((r : ℂ) • A) := by
    ext x y
    have h' : ⟪A x, y⟫ = -⟪x, A y⟫ := by
      rw [← adjoint_inner_right, hA, inner_neg_right]
    rw [← adjoint_inner_right]
    rw [h', inner_smul_left, inner_smul_right, conj_ofReal, ofReal_mul]

  theorem lie (hA : IsSkewAdjoint A) (hB : IsSkewAdjoint B) : IsSkewAdjoint (A * B - B * A) := by
    ext x y
    have h₁ : ⟪A (B x), y⟫ = -⟪B x, A y⟫ := by
      rw [← adjoint_inner_right, hA, inner_neg_right]
    have h₂ : ⟪B (A x), y⟫ = -⟪A x, B y⟫ := by
      rw [← adjoint_inner_right, hB, inner_neg_right]
    simp [h₁, h₂, sub_neg, mul_comm, mul_left_comm, mul_assoc]

end IsSkewAdjoint

/-- The type of skew-adjoint operators. -/
@[ext]
structure SkewAdjoint (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : EndH H
  isSkewAdjoint : IsSkewAdjoint op

namespace SkewAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A B : SkewAdjoint H}

/-- Negation of a skew-adjoint operator. -/
@[simp]
def neg (A : SkewAdjoint H) : SkewAdjoint H :=
  ⟨-A.op, IsSkewAdjoint.neg_adjoint A.isSkewAdjoint⟩

/-- Addition of skew-adjoint operators. -/
@[simp]
def add (A B : SkewAdjoint H) : SkewAdjoint H :=
  ⟨A.op + B.op, IsSkewAdjoint.add A.isSkewAdjoint B.isSkewAdjoint⟩

/-- Real scalar multiplication of skew-adjoint operators. -/
@[simp]
def smul (r : ℝ) (A : SkewAdjoint H) : SkewAdjoint H :=
  ⟨(r : ℂ) • A.op, IsSkewAdjoint.smul r A.isSkewAdjoint⟩

end SkewAdjoint

/-- `SkewAdjoint H` is an additive commutative group. -/
instance SkewAdjoint.addCommGroup {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : AddCommGroup (SkewAdjoint H) where
  zero := ⟨0, by simp [IsSkewAdjoint, ContinuousLinearMap.adjoint_zero]⟩
  add := SkewAdjoint.add
  neg := SkewAdjoint.neg
  zero_add := by intro A; cases A; ext x; simp
  add_zero := by intro A; cases A; ext x; simp
  add_comm := by intro A B; cases A; cases B; ext x; apply add_comm
  add_assoc := by intro A B C; cases A; cases B; cases C; ext x; apply add_assoc
  add_left_neg := by intro A; cases A; ext x; simp
  nsmul_zero := by intro A; cases A; ext x; simp
  nsmul_succ := by intro n A; cases A; ext x; simp [nsmul_succ]
  zsmul_zero' := by intro A; cases A; ext x; simp
  zsmul_succ' := by intro n A; cases A; ext x; simp [zsmul_ofNat, nsmul]
  zsmul_neg' := by intro n A; cases A; ext x; simp [zsmul_negSucc, neg_smul, nsmul]
  sub_eq_add_neg := by intro A B; cases A; cases B; ext x; simp [sub_eq_add_neg]

/-- `SkewAdjoint H` is a `ℝ`-module. -/
instance SkewAdjoint.module {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Module ℝ (SkewAdjoint H) where
  smul_add := by intro r A B; cases A; cases B; ext x; simp [smul_add]
  smul_zero := by intro r; ext x; simp
  zero_smul := by intro A; cases A; ext x; simp [(one_smul _ _).symm]
  one_smul := by intro A; cases A; ext x; simp
  mul_smul := by intro r s A; cases A; ext x; simp [mul_smul]
  add_smul := by intro r s A; cases A; ext x; simp [add_smul, smul_add]
  smul := SkewAdjoint.smul

/-- Lie bracket on `SkewAdjoint H` is the commutator. -/
def SkewAdjoint.lieBracket {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : SkewAdjoint H) : SkewAdjoint H :=
  ⟨A.op * B.op - B.op * A.op, IsSkewAdjoint.lie A.isSkewAdjoint B.isSkewAdjoint⟩

/-- `SkewAdjoint H` is a Lie ring. -/
instance SkewAdjoint.lieRing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : LieRing (SkewAdjoint H) where
  bracket := SkewAdjoint.lieBracket
  add_lie := by intro A B C; cases A; cases B; cases C; ext x; simp [lieBracket, map_add, sub_add]
  lie_add := by intro A B C; cases A; cases B; cases C; ext x; simp [lieBracket, map_add, sub_add]
  lie_self := by intro A; cases A; ext x; simp [lieBracket, sub_self]
  leibniz_lie := by
    intro A B C
    cases A; cases B; cases C
    ext x
    simp [lieBracket, mul_assoc, mul_comm, mul_left_comm]
    ring

/-- `SkewAdjoint H` is a real Lie algebra. -/
instance SkewAdjoint.lieAlgebra {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : LieAlgebra ℝ (SkewAdjoint H) where
  lie_smul := by
    intro r A B
    cases A; cases B
    ext x
    simp [smul_lie, map_smul, smul_sub, mul_smul, mul_comm]

/-! ### Projective Quantum Geometric Tensor -/

/--
**ProjectiveQGT**:
The quantum geometric tensor on the projective Hilbert space, viewed as a
pair of real bilinear forms on the bounded operator algebra `End H`.
-/
structure ProjectiveQGT (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The symmetric Riemannian (Fubini–Study) component. -/
  metric : LinearMap.BilinForm ℝ (EndH H)
  /-- The alternating Berry curvature (symplectic) component. -/
  berry : LinearMap.BilinForm ℝ (EndH H)
  /-- The metric is symmetric. -/
  metric_symm : metric.IsSymm
  /-- The Berry curvature is alternating. -/
  berry_alt : berry.IsAlt
  /-- Complex-structure action: `J(A) = Complex.I • A`. -/
  complexAction (A : EndH H) : EndH H := Complex.I • A
  /-- Kähler compatibility: `Ω(A, B) = g(A, J B)`. -/
  compat : ∀ A B, berry A B = metric A (complexAction B)

namespace ProjectiveQGT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Q : ProjectiveQGT H)

/-- Accessor for the symmetric metric component. -/
def g (Q : ProjectiveQGT H) : LinearMap.BilinForm ℝ (EndH H) := Q.metric

/-- Accessor for the antisymmetric Berry component. -/
def Ω (Q : ProjectiveQGT H) : LinearMap.BilinearForm ℝ (EndH H) := Q.berry

/-- Kähler compatibility in owner form. -/
@[simp]
theorem compat_complex_I (A B : EndH H) :
    Q.berry A B = Q.metric A (Q.complexAction B) :=
  Q.compat A B

/--
**ofState**:
Construct the QGT from a non-zero reference state `ψ`.
The metric is the real part of the local inner product,
the Berry curvature is the negative imaginary part.
-/
noncomputable def ofState (ψ : H) (hψ : ψ ≠ 0) : ProjectiveQGT H where
  metric := LinearMap.mk₂ ℝ
    (fun A B => RCLike.re (⟪A ψ, B ψ⟫_ℂ) / (‖ψ‖ ^ 2))
    (by intro A₁ A₂ B; simp [map_add, inner_add_left])
    (by intro c A B; simp [map_smul, inner_smul_left, RCLike.smul_re])
    (by intro A B₁ B₂; simp [inner_add_right])
    (by intro c A B; simp [map_smul, inner_smul_right, RCLike.smul_re])
  berry := LinearMap.mk₂ ℝ
    (fun A B => -RCLike.im (⟪A ψ, B ψ⟫_ℂ) / (‖ψ‖ ^ 2))
    (by intro A₁ A₂ B; simp [map_add, inner_add_left])
    (by intro c A B; simp [map_smul, inner_smul_left, RCLike.smul_im])
    (by intro A B₁ B₂; simp [inner_add_right])
    (by intro c A B; simp [map_smul, inner_smul_right, RCLike.smul_im])
  metric_symm := by
    intro A B
    simp [cinner_commute, conj_re]
  berry_alt := by
    intro A
    simp [sub_self]
  compat := by
    intro A B
    have h : ⟪A ψ, (Complex.I • B) ψ⟫_ℂ = Complex.I * ⟪A ψ, B ψ⟫_ℂ := by
      simp [inner_smul_right]
    have hre : RCLike.re (Complex.I * ⟪A ψ, B ψ⟫_ℂ) = -RCLike.im ⟪A ψ, B ψ⟫_ℂ := by
      simp [Complex.I_mul_re, Complex.I_mul_im, one_mul]
    simp [h, hre, smul_smul, one_smul]

/-- The metric of `ofState` evaluated at `A, B`. -/
@[simp]
theorem ofState_metric_apply (ψ : H) (hψ : ψ ≠ 0) (A B : EndH H) :
    (ofState ψ hψ).metric A B = RCLike.re (⟪A ψ, B ψ⟫_ℂ) / (‖ψ‖ ^ 2) := rfl

/-- The Berry form of `ofState` evaluated at `A, B`. -/
@[simp]
theorem ofState_berry_apply (ψ : H) (hψ : ψ ≠ 0) (A B : EndH H) :
    (ofState ψ hψ).berry A B = -RCLike.im (⟪A ψ, B ψ⟫_ℂ) / (‖ψ‖ ^ 2) := rfl

/--
**ofState_self_metric_nonneg**:
The metric evaluated on the same operator is non-negative.
-/
theorem ofState_metric_self_nonneg (ψ : H) (hψ : ψ ≠ 0) (A : EndH H) :
    0 ≤ (ofState ψ hψ).metric A A := by
  simp [ofState_metric_apply]
  have h : ⟪A ψ, A ψ⟫_ℂ = (‖A ψ‖ : ℂ) ^ 2 := by
    rw [norm_add_sq]
    <;> simp [Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_eq_abs]
    <;> ring_nf
    <;> simp [Complex.ext_iff, pow_two]
    <;> norm_num
    <;>
    (try
      {
        field_simp [Real.sqrt_eq_iff_sq_eq] <;>
        ring_nf <;>
        norm_num <;>
        linarith
      })
    <;>
    (try
      {
        simp_all [Complex.ext_iff, pow_two]
        <;>
        nlinarith
      })
  simp [h]
  apply div_nonneg
  · -- Prove that the norm squared is non-negative
    have h₁ : 0 ≤ (‖A ψ‖ : ℝ) := by positivity
    have h₂ : 0 ≤ (‖A ψ‖ : ℝ) ^ 2 := by positivity
    simp [Complex.ext_iff, pow_two] at h₂ ⊢
    <;> norm_num at h₂ ⊢ <;>
    (try positivity) <;>
    (try nlinarith)
  · -- Prove that the denominator is positive
    have h₁ : 0 < (‖ψ‖ : ℝ) := by
      apply norm_pos_iff.mpr
      exact hψ
    have h₂ : 0 < (‖ψ‖ : ℝ) ^ 2 := by positivity
    simp [Complex.ext_iff, pow_two] at h₂ ⊢
    <;> norm_num at h₂ ⊢ <;>
    (try positivity) <;>
    (try nlinarith)

/-! ### Skew-adjoint Lie representation -/

/-- The canonical inclusion of the real Lie algebra of skew-adjoint operators
into the bounded operator algebra `End H` (equipped with its associative-ring
Lie bracket).  This is a Lie-algebra homomorphism.
-/
noncomputable def SkewAdjointLieRep {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    SkewAdjoint H →ₗ⁅ℝ⁆ EndH H :=
  { toFun := fun A => A.op
    map_add' := by
      intro A B
      cases A; cases B
      ext x
      simp [SkewAdjoint.add]
    map_smul' := by
      intro r A
      cases A
      ext x
      simp [SkewAdjoint.smul]
    map_lie' := by
      intro A B
      cases A; cases B
      ext (x : H)
      simp only [SkewAdjoint.lieBracket, Ring.lie_def, SkewAdjoint.op]
      <;>
      simp [EndH, ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_sub]
      <;>
      simp_all [SkewAdjoint.lieBracket, Ring.lie_def, SkewAdjoint.op, EndH]
      <;>
      abel }

theorem SkewAdjointLieRep_map_lie {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : SkewAdjoint H) :
    SkewAdjointLieRep ⁅A, B⁆ = ⁅SkewAdjointLieRep A, SkewAdjointLieRep B⁆ :=
  LieHom.map_lie _ A B

theorem SkewAdjointLieRep_injective {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Function.Injective SkewAdjointLieRep :=
  fun A B h => by
    cases A; cases B
    simp at h
    exact Subtype.coe_injective h

end ProjectiveQGT

end InfoGeometry.QuantumGeometry.Projective
