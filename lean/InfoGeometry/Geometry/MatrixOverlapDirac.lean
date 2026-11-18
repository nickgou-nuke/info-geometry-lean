/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.MatrixSpectralSign
import InfoGeometry.OperatorAlgebra.GinspargWilson

/-!
# Finite overlap Dirac operators from native spectral calculus

For an invertible Hermitian matrix `H`, the sign in `D = 1 + Γ * sign H`
is constructed by Mathlib, not supplied as an involution assumption. The
chirality `Γ` is a Hermitian involution; it need not commute with `H`.

The existing Ginsparg--Wilson owner uses `D = 1 - gamma.chi * epsilon.chi`.
The explicit compatibility map below supplies `epsilon.chi = -sign H`, with
its involution law derived from the actual functional-calculus construction.
That owner's chiral projectors and intertwining theorems are reused directly.

These are dimensionless, unit-spacing identities corresponding to equations
(2.6)--(2.9) of arXiv:2610.09093v1. No Wilson-link construction, uniform family
gap, locality, determinant transport, or fermion measure is asserted here.
The real example retains the full noncommutative matrix product. The same
general theorems apply to complex matrices without discarding their phase.
-/

noncomputable section

namespace InfoGeometry.Geometry.MatrixOverlapDirac

open InfoGeometry.Analysis.MatrixSpectralSign
open InfoGeometry.OperatorAlgebra

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The unit-spacing overlap operator with its actual native spectral sign. -/
def overlapDirac (Γ H : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  1 + Γ * spectralSign H

/-- The positive spectral projector, equal to the negative modified-chirality
projector when the reference chirality squares to one. -/
def positiveSpectralProjector (H : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (1 / 2 : ℝ) • (1 + spectralSign H)

/-- The actual negative spectral sign as an input to the existing chiral
involution owner. Its square law follows from Hermiticity and invertibility. -/
def negativeSignInvolution (H : Matrix n n 𝕜)
    (hH : H.IsHermitian) (hunit : IsUnit H) : ChiralInvolution (Matrix n n 𝕜) where
  chi := -spectralSign H
  chi_sq := by rw [neg_mul_neg, spectralSign_mul_self hH hunit]

/-- Compatibility with the existing overlap convention `1 - gamma * epsilon`. -/
theorem overlapDirac_eq_ginspargWilson (gamma : ChiralInvolution (Matrix n n 𝕜))
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) (hunit : IsUnit H) :
    overlapDirac gamma.chi H =
      GinspargWilson.overlapDirac gamma (negativeSignInvolution H hH hunit) := by
  simp only [overlapDirac, GinspargWilson.overlapDirac, negativeSignInvolution,
    mul_neg, sub_neg_eq_add]

/-- The native positive spectral projector is the existing right projector of
the negative spectral involution. -/
theorem positiveSpectralProjector_eq_Pright {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (hunit : IsUnit H) :
    positiveSpectralProjector H = (negativeSignInvolution H hH hunit).Pright := by
  simp only [positiveSpectralProjector, ChiralInvolution.Pright,
    negativeSignInvolution, sub_neg_eq_add]

/-- The constructed matrix sign supplies the second involution to the existing
noncommutative Ginsparg--Wilson theorem. -/
theorem ginspargWilson {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) (hH : H.IsHermitian) (hunit : IsUnit H) :
    Γ * overlapDirac Γ H + overlapDirac Γ H * Γ =
      overlapDirac Γ H * Γ * overlapDirac Γ H := by
  let gamma : ChiralInvolution (Matrix n n 𝕜) := ⟨Γ, hΓ⟩
  change gamma.chi * overlapDirac gamma.chi H + overlapDirac gamma.chi H * gamma.chi =
    overlapDirac gamma.chi H * gamma.chi * overlapDirac gamma.chi H
  rw [overlapDirac_eq_ginspargWilson gamma hH hunit]
  exact GinspargWilson.overlapDirac_ginspargWilson gamma (negativeSignInvolution H hH hunit)

/-- Adjoint conjugation needs Hermitian chirality, but does not require
commutation between the two inputs or an invertible kernel. -/
theorem gammaHermitian {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) (hΓstar : Γ.IsHermitian) :
    star (overlapDirac Γ H) = Γ * overlapDirac Γ H * Γ := by
  have hleft : Γ * overlapDirac Γ H = Γ + spectralSign H := by
    simp only [overlapDirac, mul_add, mul_one, ← mul_assoc, hΓ, one_mul]
  rw [hleft, add_mul, hΓ]
  simp only [overlapDirac, star_add, star_one, star_mul,
    (spectralSign_isHermitian H).isSelfAdjoint.star_eq, hΓstar.isSelfAdjoint.star_eq]

/-- Modified chirality has the paper's minus sign, including for kernels
whose spectral sign is not an involution. -/
theorem modifiedChirality_eq_neg_sign {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) :
    Γ * (1 - overlapDirac Γ H) = -spectralSign H := by
  unfold overlapDirac
  have hsub : (1 : Matrix n n 𝕜) - (1 + Γ * spectralSign H) = -(Γ * spectralSign H) := by
    abel
  rw [hsub, mul_neg, ← mul_assoc, hΓ, one_mul]

/-- The reference chirality's square and the constructed sign make modified
chirality an involution. -/
theorem modifiedChirality_mul_self {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) (hH : H.IsHermitian) (hunit : IsUnit H) :
    (Γ * (1 - overlapDirac Γ H)) * (Γ * (1 - overlapDirac Γ H)) = 1 := by
  rw [modifiedChirality_eq_neg_sign hΓ, neg_mul_neg, spectralSign_mul_self hH hunit]

/-- The positive spectral projector is an actual idempotent, by the existing
chiral-involution projector theorem. -/
theorem positiveSpectralProjector_isIdempotentElem {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (hunit : IsUnit H) :
    IsIdempotentElem (positiveSpectralProjector H) := by
  rw [positiveSpectralProjector_eq_Pright hH hunit]
  exact (negativeSignInvolution H hH hunit).Pright_idem

/-- The same native positive projector is Hermitian. Together with the
idempotence theorem, this is an orthogonal spectral projection. -/
theorem positiveSpectralProjector_isHermitian (H : Matrix n n 𝕜) :
    (positiveSpectralProjector H).IsHermitian :=
  (IsSelfAdjoint.all (1 / 2 : ℝ)).smul
    ((IsSelfAdjoint.one (Matrix n n 𝕜)).add (spectralSign_isHermitian H).isSelfAdjoint)

/-- The negative modified-chirality sector selects the positive spectrum
of the Hermitian kernel. -/
theorem positiveSpectralProjector_eq_modifiedMinus {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) :
    positiveSpectralProjector H =
      (1 / 2 : ℝ) • (1 - Γ * (1 - overlapDirac Γ H)) := by
  simp only [positiveSpectralProjector, modifiedChirality_eq_neg_sign hΓ, sub_neg_eq_add]

/-- The fermion and antifermion chirality constraints intertwine by the
existing two-involution theorem, with the actual constructed sign as input. -/
theorem intertwining {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) (hH : H.IsHermitian) (hunit : IsUnit H) :
    overlapDirac Γ H * positiveSpectralProjector H =
      ((1 / 2 : ℝ) • (1 + Γ)) * overlapDirac Γ H := by
  let gamma : ChiralInvolution (Matrix n n 𝕜) := ⟨Γ, hΓ⟩
  rw [positiveSpectralProjector_eq_Pright hH hunit]
  change overlapDirac gamma.chi H * (negativeSignInvolution H hH hunit).Pright =
    gamma.Pleft * overlapDirac gamma.chi H
  rw [overlapDirac_eq_ginspargWilson gamma hH hunit]
  exact GinspargWilson.overlapDirac_mul_Pright gamma (negativeSignInvolution H hH hunit)

/-- An invertible kernel need not yield an invertible overlap operator:
the actual spectral-calculus construction gives zero for `H = -Γ`. -/
theorem overlapDirac_neg_chirality {Γ : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) (hΓstar : Γ.IsHermitian) :
    IsUnit (-Γ) ∧ overlapDirac Γ (-Γ) = 0 := by
  have hsquare : (-Γ) * (-Γ) = 1 := by simpa only [neg_mul_neg] using hΓ
  refine ⟨⟨⟨-Γ, -Γ, hsquare, hsquare⟩, rfl⟩, ?_⟩
  unfold overlapDirac
  rw [spectralSign_eq_self_of_mul_self hΓstar.neg hsquare, mul_neg, hΓ]
  exact add_neg_cancel 1

section NoncommutingExample

/-- A concrete real chirality on the full two-dimensional matrix algebra. -/
def exampleChirality : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- A noncommuting Hermitian kernel, not a claim about a Wilson-link family. -/
def exampleKernel : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem exampleChirality_isHermitian : exampleChirality.IsHermitian := by
  change exampleChirality.conjTranspose = exampleChirality
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [exampleChirality, Matrix.conjTranspose_apply]

theorem exampleKernel_isHermitian : exampleKernel.IsHermitian := by
  change exampleKernel.conjTranspose = exampleKernel
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [exampleKernel, Matrix.conjTranspose_apply]

theorem exampleChirality_mul_self : exampleChirality * exampleChirality = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exampleChirality, Matrix.mul_apply, Fin.sum_univ_two]

theorem exampleKernel_mul_self : exampleKernel * exampleKernel = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exampleKernel, Matrix.mul_apply, Fin.sum_univ_two]

theorem exampleKernel_isUnit : IsUnit exampleKernel :=
  ⟨⟨exampleKernel, exampleKernel, exampleKernel_mul_self, exampleKernel_mul_self⟩, rfl⟩

/-- This concrete pair rules out an accidental commuting specialization. -/
theorem example_not_commute :
    exampleChirality * exampleKernel ≠ exampleKernel * exampleChirality := by
  intro hcomm
  have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hcomm
  norm_num [exampleChirality, exampleKernel, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- The noncommuting example computes the sign through the same native
functional calculus used by the general theorem. -/
theorem example_overlapDirac :
    overlapDirac exampleChirality exampleKernel = !![1, 1; -1, 1] := by
  unfold overlapDirac
  rw [spectralSign_eq_self_of_mul_self exampleKernel_isHermitian exampleKernel_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exampleChirality, exampleKernel, Matrix.mul_apply, Fin.sum_univ_two]

end NoncommutingExample

end InfoGeometry.Geometry.MatrixOverlapDirac

end
