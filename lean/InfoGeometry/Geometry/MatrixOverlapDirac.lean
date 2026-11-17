/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.MatrixSpectralSign
import InfoGeometry.Algebra.OverlapDirac

/-!
# Finite overlap Dirac operators from native spectral calculus

For an invertible Hermitian matrix `H`, the sign in `D = 1 + Γ * sign H`
is constructed by Mathlib, not supplied as an involution assumption. The
chirality `Γ` is a Hermitian involution; it need not commute with `H`.

These are dimensionless, unit-spacing identities corresponding to equations
(2.6)--(2.9) of arXiv:2610.09093v1. No Wilson-link construction, uniform family
gap, locality, determinant transport, or fermion measure is asserted here.
The real example retains the full noncommutative matrix product. The same
general theorems apply to complex matrices without discarding their phase.
-/

noncomputable section

namespace InfoGeometry.Geometry.MatrixOverlapDirac

open InfoGeometry.Analysis.MatrixSpectralSign
open InfoGeometry.Algebra.CyclotomicOperatorProjectors

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The unit-spacing overlap operator with its actual native spectral sign. -/
def overlapDirac (Γ H : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  Algebra.OverlapDirac.overlapDirac Γ (spectralSign H)

/-- The positive spectral projector, equal to the negative modified-chirality
projector when the reference chirality squares to one. -/
def positiveSpectralProjector (H : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (1 / 2 : ℝ) • (1 + spectralSign H)

/-- The constructed matrix sign discharges the noncommutative overlap
identity's sign-involution hypothesis. -/
theorem ginspargWilson {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) (hH : H.IsHermitian) (hunit : IsUnit H) :
    Γ * overlapDirac Γ H + overlapDirac Γ H * Γ =
      overlapDirac Γ H * Γ * overlapDirac Γ H :=
  Algebra.OverlapDirac.ginspargWilson hΓ (spectralSign_mul_self hH hunit)

/-- Adjoint conjugation needs Hermitian chirality, but does not require
commutation between the two inputs. -/
theorem gammaHermitian {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) (hΓstar : Γ.IsHermitian) :
    star (overlapDirac Γ H) = Γ * overlapDirac Γ H * Γ :=
  Algebra.OverlapDirac.gammaHermitian hΓ hΓstar.isSelfAdjoint
    (spectralSign_isHermitian H).isSelfAdjoint

/-- Modified chirality has the paper's minus sign. -/
theorem modifiedChirality_eq_neg_sign {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) :
    Γ * (1 - overlapDirac Γ H) = -spectralSign H :=
  Algebra.OverlapDirac.modifiedChirality_eq_neg hΓ

/-- The reference chirality's square and the constructed sign make modified
chirality an involution. -/
theorem modifiedChirality_mul_self {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) (hH : H.IsHermitian) (hunit : IsUnit H) :
    (Γ * (1 - overlapDirac Γ H)) * (Γ * (1 - overlapDirac Γ H)) = 1 :=
  Algebra.OverlapDirac.modifiedChirality_mul_self hΓ (spectralSign_mul_self hH hunit)

/-- The positive spectral projector is an actual idempotent. The existing
noncommutative involution-projector theorem supplies the algebraic step. -/
theorem positiveSpectralProjector_isIdempotentElem {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (hunit : IsUnit H) :
    IsIdempotentElem (positiveSpectralProjector H) := by
  have hhalf : (2 : Matrix n n 𝕜) * algebraMap ℝ (Matrix n n 𝕜) (1 / 2) = 1 := by
    calc
      (2 : Matrix n n 𝕜) * algebraMap ℝ (Matrix n n 𝕜) (1 / 2) =
          algebraMap ℝ (Matrix n n 𝕜) ((2 : ℝ) * (1 / 2)) := by
        simp only [map_mul, map_ofNat]
      _ = 1 := by norm_num
  have hsquare : spectralSign H ^ 2 = 1 := by
    rw [pow_two, spectralSign_mul_self hH hunit]
  simpa only [IsIdempotentElem, IsIdempotent, involutionPlusProjector,
    positiveSpectralProjector, Algebra.smul_def] using
    involution_plus_isIdempotent_of_commute hhalf
      (Algebra.commute_algebraMap_left (1 / 2 : ℝ) (spectralSign H)) hsquare

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
      Algebra.OverlapDirac.modifiedMinusProjector Γ (spectralSign H) :=
  (Algebra.OverlapDirac.modifiedMinusProjector_eq_signPlus hΓ).symm

/-- The fermion and antifermion chirality constraints intertwine with the
operator constructed from `H`; no scalar or commuting surrogate is used. -/
theorem intertwining {Γ H : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) (hH : H.IsHermitian) (hunit : IsUnit H) :
    overlapDirac Γ H * positiveSpectralProjector H =
      ((1 / 2 : ℝ) • (1 + Γ)) * overlapDirac Γ H := by
  rw [positiveSpectralProjector_eq_modifiedMinus hΓ]
  exact Algebra.OverlapDirac.intertwining hΓ (spectralSign_mul_self hH hunit)

/-- An invertible kernel need not yield an invertible overlap operator:
the actual spectral-calculus construction gives zero for `H = -Γ`. -/
theorem overlapDirac_neg_chirality {Γ : Matrix n n 𝕜}
    (hΓ : Γ * Γ = 1) (hΓstar : Γ.IsHermitian) :
    IsUnit (-Γ) ∧ overlapDirac Γ (-Γ) = 0 := by
  have hsquare : (-Γ) * (-Γ) = 1 := by simpa only [neg_mul_neg] using hΓ
  refine ⟨⟨⟨-Γ, -Γ, hsquare, hsquare⟩, rfl⟩, ?_⟩
  unfold overlapDirac Algebra.OverlapDirac.overlapDirac
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
  unfold overlapDirac Algebra.OverlapDirac.overlapDirac
  rw [spectralSign_eq_self_of_mul_self exampleKernel_isHermitian exampleKernel_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exampleChirality, exampleKernel, Matrix.mul_apply, Fin.sum_univ_two]

end NoncommutingExample

end InfoGeometry.Geometry.MatrixOverlapDirac

end
