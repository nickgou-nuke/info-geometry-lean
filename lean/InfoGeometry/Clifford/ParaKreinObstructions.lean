/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Algebraic obstructions and normalization for a neutral potential

The carrier, neutral bilinear form, para-involution, and evaluation quadratic
form are the existing owners in `NeutralPhaseSpaceCore`. On this actual
`E × Module.Dual ℝ E` carrier the proposed quadratic expression `B(X, K X)`
vanishes. The corrected flat potential is the existing evaluation form, equal
to `B(X, X) / 2`; its second finite difference recovers `B`.

The remaining results concern arbitrary real bilinear forms and arbitrary
noncommutative real algebras. A real symmetric form has zero diagonal
expectation against a skew-adjoint operator. A positive scalar multiple of
an involution is an involution only at scalar one, on a nontrivial algebra.

These algebraic statements do not assert a Mukai pairing in every dimension,
a global para-Kähler manifold, a Gibbs measure, or a dissipation theorem.
-/

namespace InfoGeometry.Clifford.ParaKreinObstructions

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

section NeutralPotential

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The para-involution cannot generate a real scalar potential through the
diagonal of the symmetric neutral pairing. -/
@[rep_depth operator, simp]
theorem canonicalNeutralBilin_self_para (X : PhaseSpaceCarrier E) :
    canonicalNeutralBilin X (neutralParaInvolution X) = 0 := by
  simp [canonicalNeutralBilin_apply, neutralParaInvolution_apply]

/-- The existing unscaled evaluation form is the correctly normalized
quadratic potential for the symmetric neutral pairing. -/
@[rep_depth operator]
theorem canonicalNeutralFormUnscaled_eq_half_self (X : PhaseSpaceCarrier E) :
    canonicalNeutralFormUnscaled X = (1 / 2 : ℝ) * canonicalNeutralBilin X X := by
  simp only [canonicalNeutralFormUnscaled_apply, canonicalNeutralBilin_apply]
  ring

/-- The second finite difference of the flat potential is independent of
the base point and recovers the actual neutral bilinear form. -/
@[rep_depth operator]
theorem canonicalNeutralFormUnscaled_second_difference
    (X U V : PhaseSpaceCarrier E) :
    canonicalNeutralFormUnscaled (X + U + V) -
        canonicalNeutralFormUnscaled (X + U) -
        canonicalNeutralFormUnscaled (X + V) +
        canonicalNeutralFormUnscaled X = canonicalNeutralBilin U V := by
  have h₁ := canonicalNeutralFormUnscaled_polar (X + U) V
  have h₂ := canonicalNeutralFormUnscaled_polar X V
  have hadd : canonicalNeutralBilin (X + U) V =
      canonicalNeutralBilin X V + canonicalNeutralBilin U V := by
    simp only [map_add, LinearMap.add_apply]
  simp only [QuadraticMap.polar] at h₁ h₂
  rw [hadd] at h₁
  linarith

end NeutralPotential

section SkewAdjointExpectation

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- For a real symmetric bilinear form, the diagonal expectation of a
skew-adjoint endomorphism is zero. In particular this expression cannot
be a nonconstant real momentum function. -/
@[rep_depth operator]
theorem symmetric_skewAdjoint_self_eq_zero
    (g : LinearMap.BilinForm ℝ E) (hg : g.IsSymm)
    (A : Module.End ℝ E) (hA : g.IsSkewAdjoint A) (x : E) :
    g x (A x) = 0 := by
  have hskew : g (A x) x = -g x (A x) := by
    simpa using hA x x
  have hsymm := hg.eq (A x) x
  exact eq_zero_of_neg_eq (hskew.symm.trans hsymm)

end SkewAdjointExpectation

section InvolutionRescaling

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Scalar rescaling preserves the ordered operator product and multiplies
the square of an involution by the square of the scalar. -/
@[rep_depth operator]
theorem smul_involution_mul_self (J : A) (hJ : J * J = 1) (c : ℝ) :
    (c • J) * (c • J) = (c * c) • (1 : A) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hJ]

/-- On a nontrivial real algebra the exact rescaling condition is `c² = 1`.
No commutativity assumption on the algebra or its operators is used. -/
@[rep_depth operator]
theorem smul_involution_iff [Nontrivial A]
    (J : A) (hJ : J * J = 1) (c : ℝ) :
    (c • J) * (c • J) = 1 ↔ c * c = 1 := by
  rw [smul_involution_mul_self J hJ]
  constructor
  · intro h
    apply smul_left_injective ℝ (one_ne_zero : (1 : A) ≠ 0)
    simpa using h
  · intro h
    simp [h]

/-- A positive rescaling of an involution remains an involution precisely
when the rescaling is trivial. This applies in particular to real
endomorphism algebras, including fundamental symmetries. -/
@[rep_depth operator]
theorem positive_smul_involution_iff [Nontrivial A]
    (J : A) (hJ : J * J = 1) (c : ℝ) (hc : 0 < c) :
    (c • J) * (c • J) = 1 ↔ c = 1 := by
  rw [smul_involution_iff J hJ]
  constructor
  · intro h
    have hfactor : (c - 1) * (c + 1) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · linarith only [hminus]
    · linarith only [hc, hplus]
  · intro h
    simp [h]

end InvolutionRescaling

end InfoGeometry.Clifford.ParaKreinObstructions
