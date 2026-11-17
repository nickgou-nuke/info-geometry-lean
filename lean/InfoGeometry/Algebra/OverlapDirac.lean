/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CyclotomicOperatorProjectors

/-!
# Noncommutative overlap Dirac identities

The unit-spacing overlap operator is `D = 1 + Γ * ε`. Two involution
identities imply the Ginsparg--Wilson relation and the modified chirality
`Γ * (1 - D) = -ε`; no commutation of `Γ` and `ε` is assumed.

The adjoint statement additionally assumes that both inputs are self-adjoint.
The real half-projector identities reuse the existing cyclotomic involution
projectors. In particular the modified negative projector is the positive
projector of `ε`, and `D` intertwines it with the positive projector of `Γ`.

This file is algebraic. Constructing `ε` as the spectral sign of an invertible
Hermitian matrix belongs to `InfoGeometry.Analysis.MatrixSpectralSign`.
-/

namespace InfoGeometry.Algebra.OverlapDirac

open CyclotomicOperatorProjectors

variable {A : Type*} [Ring A] {Γ ε : A}

/-- The overlap Dirac operator at unit lattice spacing. -/
def overlapDirac (Γ ε : A) : A := 1 + Γ * ε

/-- Chirality modified by the overlap Dirac operator. -/
def modifiedChirality (Γ ε : A) : A := Γ * (1 - overlapDirac Γ ε)

/-- Left multiplication by the grading reduces to the sum of the two inputs. -/
theorem gamma_mul_overlapDirac (hΓ : Γ * Γ = 1) :
    Γ * overlapDirac Γ ε = Γ + ε := by
  unfold overlapDirac
  rw [mul_add, mul_one, ← mul_assoc, hΓ, one_mul]

/-- The two involutions give an ordered intertwining identity. -/
theorem overlapDirac_mul_epsilon (hΓ : Γ * Γ = 1) (hε : ε * ε = 1) :
    overlapDirac Γ ε * ε = Γ * overlapDirac Γ ε := by
  rw [gamma_mul_overlapDirac hΓ]
  unfold overlapDirac
  rw [add_mul, one_mul, mul_assoc, hε, mul_one]
  exact add_comm _ _

/-- The overlap operator is Hermitian after twisting by the grading. -/
theorem gammaHermitian [StarRing A] (hΓ : Γ * Γ = 1)
    (hΓstar : IsSelfAdjoint Γ) (hεstar : IsSelfAdjoint ε) :
    star (overlapDirac Γ ε) = Γ * overlapDirac Γ ε * Γ := by
  calc
    star (overlapDirac Γ ε) = 1 + ε * Γ := by
      simp only [overlapDirac, star_add, star_one, star_mul,
        hεstar.star_eq, hΓstar.star_eq]
    _ = (Γ + ε) * Γ := by rw [add_mul, hΓ]
    _ = Γ * overlapDirac Γ ε * Γ := by rw [gamma_mul_overlapDirac hΓ]

/-- The unit-spacing Ginsparg--Wilson relation in the full noncommutative ring. -/
theorem ginspargWilson (hΓ : Γ * Γ = 1) (hε : ε * ε = 1) :
    Γ * overlapDirac Γ ε + overlapDirac Γ ε * Γ =
      overlapDirac Γ ε * Γ * overlapDirac Γ ε := by
  calc
    Γ * overlapDirac Γ ε + overlapDirac Γ ε * Γ =
        overlapDirac Γ ε * ε + overlapDirac Γ ε * Γ := by
      rw [overlapDirac_mul_epsilon hΓ hε]
    _ = overlapDirac Γ ε * (Γ + ε) := by
      rw [mul_add]
      exact add_comm _ _
    _ = overlapDirac Γ ε * (Γ * overlapDirac Γ ε) := by
      rw [gamma_mul_overlapDirac hΓ]
    _ = overlapDirac Γ ε * Γ * overlapDirac Γ ε := (mul_assoc _ _ _).symm

/-- The modified grading has the opposite sign to the spectral involution. -/
theorem modifiedChirality_eq_neg (hΓ : Γ * Γ = 1) :
    modifiedChirality Γ ε = -ε := by
  unfold modifiedChirality overlapDirac
  have hsub : (1 : A) - (1 + Γ * ε) = -(Γ * ε) := by abel
  rw [hsub, mul_neg, ← mul_assoc, hΓ, one_mul]

/-- The modified chirality is an involution. -/
theorem modifiedChirality_mul_self (hΓ : Γ * Γ = 1) (hε : ε * ε = 1) :
    modifiedChirality Γ ε * modifiedChirality Γ ε = 1 := by
  rw [modifiedChirality_eq_neg hΓ, neg_mul_neg, hε]

/-- Self-adjointness of the spectral involution passes to the modified chirality. -/
theorem modifiedChirality_isSelfAdjoint [StarRing A] (hΓ : Γ * Γ = 1)
    (hεstar : IsSelfAdjoint ε) : IsSelfAdjoint (modifiedChirality Γ ε) := by
  rw [modifiedChirality_eq_neg hΓ]
  exact hεstar.neg

/-- The overlap operator changes modified chirality into the negative original chirality. -/
theorem overlapDirac_mul_modifiedChirality (hΓ : Γ * Γ = 1) (hε : ε * ε = 1) :
    overlapDirac Γ ε * modifiedChirality Γ ε = -(Γ * overlapDirac Γ ε) := by
  rw [modifiedChirality_eq_neg hΓ, mul_neg, overlapDirac_mul_epsilon hΓ hε]

section RealProjectors

variable [Algebra ℝ A]

noncomputable section

/-- The positive projector of the modified chirality. -/
def modifiedPlusProjector (Γ ε : A) : A :=
  (1 / 2 : ℝ) • (1 + modifiedChirality Γ ε)

/-- The negative projector of the modified chirality. -/
def modifiedMinusProjector (Γ ε : A) : A :=
  (1 / 2 : ℝ) • (1 - modifiedChirality Γ ε)

private theorem two_mul_realHalf : (2 : A) * algebraMap ℝ A (1 / 2) = 1 := by
  calc
    (2 : A) * algebraMap ℝ A (1 / 2) =
        algebraMap ℝ A ((2 : ℝ) * (1 / 2)) := by simp only [map_mul, map_ofNat]
    _ = 1 := by norm_num

/-- The modified positive projector selects the negative spectral sign. -/
theorem modifiedPlusProjector_eq_signMinus (hΓ : Γ * Γ = 1) :
    modifiedPlusProjector Γ ε = (1 / 2 : ℝ) • (1 - ε) := by
  rw [modifiedPlusProjector, modifiedChirality_eq_neg hΓ, ← sub_eq_add_neg]

/-- The modified negative projector selects the positive spectral sign. -/
theorem modifiedMinusProjector_eq_signPlus (hΓ : Γ * Γ = 1) :
    modifiedMinusProjector Γ ε = (1 / 2 : ℝ) • (1 + ε) := by
  rw [modifiedMinusProjector, modifiedChirality_eq_neg hΓ, sub_neg_eq_add]

/-- Idempotence is inherited from the existing noncommutative involution projector. -/
theorem modifiedPlusProjector_isIdempotentElem (hΓ : Γ * Γ = 1) (hε : ε * ε = 1) :
    IsIdempotentElem (modifiedPlusProjector Γ ε) := by
  have hχ : modifiedChirality Γ ε ^ 2 = 1 := by
    rw [pow_two, modifiedChirality_mul_self hΓ hε]
  have hp := involution_plus_isIdempotent_of_commute (two_mul_realHalf (A := A))
    (Algebra.commute_algebraMap_left (1 / 2 : ℝ) (modifiedChirality Γ ε)) hχ
  simpa only [IsIdempotentElem, IsIdempotent, involutionPlusProjector,
    modifiedPlusProjector, Algebra.smul_def] using hp

/-- Idempotence is inherited from the existing noncommutative involution projector. -/
theorem modifiedMinusProjector_isIdempotentElem (hΓ : Γ * Γ = 1) (hε : ε * ε = 1) :
    IsIdempotentElem (modifiedMinusProjector Γ ε) := by
  have hχ : modifiedChirality Γ ε ^ 2 = 1 := by
    rw [pow_two, modifiedChirality_mul_self hΓ hε]
  have hp := involution_minus_isIdempotent_of_commute (two_mul_realHalf (A := A))
    (Algebra.commute_algebraMap_left (1 / 2 : ℝ) (modifiedChirality Γ ε)) hχ
  simpa only [IsIdempotentElem, IsIdempotent, involutionMinusProjector,
    modifiedMinusProjector, Algebra.smul_def] using hp

/-- The modified projectors resolve the identity. -/
theorem modifiedProjectors_add (Γ ε : A) :
    modifiedPlusProjector Γ ε + modifiedMinusProjector Γ ε = 1 := by
  have hp := involution_projectors_sum_eq_one
    (u := modifiedChirality Γ ε) (two_mul_realHalf (A := A))
  simpa only [involutionPlusProjector, involutionMinusProjector,
    modifiedPlusProjector, modifiedMinusProjector, Algebra.smul_def] using hp

/-- The product of the two modified projectors vanishes in the stated order. -/
theorem modifiedPlusProjector_mul_modifiedMinusProjector
    (hΓ : Γ * Γ = 1) (hε : ε * ε = 1) :
    modifiedPlusProjector Γ ε * modifiedMinusProjector Γ ε = 0 := by
  have hχ : modifiedChirality Γ ε ^ 2 = 1 := by
    rw [pow_two, modifiedChirality_mul_self hΓ hε]
  have hp := involution_projectors_orthogonal_of_commute
    (Algebra.commute_algebraMap_left (1 / 2 : ℝ) (modifiedChirality Γ ε)) hχ
  simpa only [involutionPlusProjector, involutionMinusProjector,
    modifiedPlusProjector, modifiedMinusProjector, Algebra.smul_def] using hp

/-- Orthogonality also holds in the reverse order. -/
theorem modifiedMinusProjector_mul_modifiedPlusProjector
    (hΓ : Γ * Γ = 1) (hε : ε * ε = 1) :
    modifiedMinusProjector Γ ε * modifiedPlusProjector Γ ε = 0 := by
  have hminus : modifiedMinusProjector Γ ε = 1 - modifiedPlusProjector Γ ε := by
    rw [← modifiedProjectors_add Γ ε]
    abel
  rw [hminus, sub_mul, one_mul,
    (modifiedPlusProjector_isIdempotentElem hΓ hε).eq, sub_self]

/-- The positive modified projector is self-adjoint for a self-adjoint spectral involution. -/
theorem modifiedPlusProjector_isSelfAdjoint [StarRing A] [StarModule ℝ A]
    (hΓ : Γ * Γ = 1) (hεstar : IsSelfAdjoint ε) :
    IsSelfAdjoint (modifiedPlusProjector Γ ε) :=
  (IsSelfAdjoint.all (1 / 2 : ℝ)).smul
    ((IsSelfAdjoint.one A).add (modifiedChirality_isSelfAdjoint hΓ hεstar))

/-- The negative modified projector is self-adjoint for a self-adjoint spectral involution. -/
theorem modifiedMinusProjector_isSelfAdjoint [StarRing A] [StarModule ℝ A]
    (hΓ : Γ * Γ = 1) (hεstar : IsSelfAdjoint ε) :
    IsSelfAdjoint (modifiedMinusProjector Γ ε) :=
  (IsSelfAdjoint.all (1 / 2 : ℝ)).smul
    ((IsSelfAdjoint.one A).sub (modifiedChirality_isSelfAdjoint hΓ hεstar))

/-- The overlap operator intertwines modified negative and original positive chirality. -/
theorem intertwining (hΓ : Γ * Γ = 1) (hε : ε * ε = 1) :
    overlapDirac Γ ε * modifiedMinusProjector Γ ε =
      ((1 / 2 : ℝ) • (1 + Γ)) * overlapDirac Γ ε := by
  have h : overlapDirac Γ ε * (1 - modifiedChirality Γ ε) =
      (1 + Γ) * overlapDirac Γ ε := by
    rw [mul_sub, mul_one, overlapDirac_mul_modifiedChirality hΓ hε,
      sub_neg_eq_add, add_mul, one_mul]
  simpa only [modifiedMinusProjector, mul_smul_comm, smul_mul_assoc] using
    congrArg (fun x : A => (1 / 2 : ℝ) • x) h

end

end RealProjectors

end InfoGeometry.Algebra.OverlapDirac
