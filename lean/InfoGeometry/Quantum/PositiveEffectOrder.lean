/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.PositiveBoundaryConditioning

/-!
# Loewner order detected by positive measurement effects

For finite complex matrices, positive trace tests detect the native Loewner
order. It is enough to test the effects between zero and the identity: each
nonzero vector supplies a normalized rank-one star projection.

The resulting operator-domination criterion is the measurement-effect
criterion for max-relative entropy in Eq. (150), page 32 of
*Entropic measures of quantum information*, arXiv:2611.08254v1.
No commutation or simultaneous diagonalization is assumed.
-/

noncomputable section
namespace InfoGeometry.Quantum.PositiveEffectOrder

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pairing with a native rank-one matrix reads the corresponding quadratic form. -/
theorem trace_mul_vecMulVec_self_star (A : Matrix n n ℂ) (x : n → ℂ) :
    trace (A * vecMulVec x (star x)) = star x ⬝ᵥ (A *ᵥ x) := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

/-- A positive trace test preserves Loewner comparisons, without requiring
the test to commute with either matrix. -/
theorem trace_mul_le_of_le {A B E : Matrix n n ℂ}
    (hAB : A ≤ B) (hE : E.PosSemidef) :
    trace (A * E) ≤ trace (B * E) := by
  have h := BoundaryConditioning.trace_pairing_nonneg
    (Matrix.le_iff.mp hAB) hE
  rw [sub_mul, trace_sub] at h
  exact sub_nonneg.mp h

/-- Positive semidefinite trace tests detect the full Loewner order on
Hermitian matrices. -/
theorem le_iff_trace_mul_le_posSemidef {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ≤ B ↔ ∀ E : Matrix n n ℂ, E.PosSemidef →
      trace (A * E) ≤ trace (B * E) := by
  constructor
  · intro hAB E hE
    exact trace_mul_le_of_le hAB hE
  · intro h
    rw [Matrix.le_iff]
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
    intro x
    have htrace : 0 ≤ trace ((B - A) * vecMulVec x (star x)) := by
      simpa only [sub_mul, trace_sub] using
        sub_nonneg.mpr (h _ (posSemidef_vecMulVec_self_star x))
    simpa only [trace_mul_vecMulVec_self_star] using htrace

/-- Normalizing a nonzero native rank-one matrix by its quadratic norm gives
a star projection, hence a measurement effect. -/
theorem normalized_vecMulVec_isStarProjection {x : n → ℂ} (hx : x ≠ 0) :
    IsStarProjection ((star x ⬝ᵥ x)⁻¹ • vecMulVec x (star x)) := by
  let s : ℂ := star x ⬝ᵥ x
  let K : Matrix n n ℂ := vecMulVec x (star x)
  have hs : 0 < s := Matrix.dotProduct_star_self_pos_iff.mpr hx
  have hK : K.PosSemidef := posSemidef_vecMulVec_self_star x
  have hE : (s⁻¹ • K).PosSemidef :=
    hK.smul (RCLike.inv_pos_of_pos hs).le
  have hKK : K * K = s • K := by
    dsimp only [K, s]
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  refine ⟨?_, hE.isHermitian.isSelfAdjoint⟩
  change (s⁻¹ • K) * (s⁻¹ • K) = s⁻¹ • K
  rw [smul_mul_smul_comm, hKK, smul_smul]
  simp only [mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]

/-- Every Loewner comparison between Hermitian matrices is detected by the
measurement effects between zero and the identity. -/
theorem le_iff_trace_mul_le_effects {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ≤ B ↔ ∀ E : Matrix n n ℂ, 0 ≤ E ∧ E ≤ 1 →
      trace (A * E) ≤ trace (B * E) := by
  constructor
  · intro hAB E hE
    exact trace_mul_le_of_le hAB hE.1.posSemidef
  · intro h
    rw [Matrix.le_iff]
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · let s : ℂ := star x ⬝ᵥ x
      let K : Matrix n n ℂ := vecMulVec x (star x)
      have hs : 0 < s := Matrix.dotProduct_star_self_pos_iff.mpr hx
      have hE : IsStarProjection (s⁻¹ • K) :=
        normalized_vecMulVec_isStarProjection hx
      have htrace : 0 ≤ trace ((B - A) * (s⁻¹ • K)) := by
        simpa only [sub_mul, trace_sub] using
          sub_nonneg.mpr (h _ ⟨hE.nonneg, hE.le_one⟩)
      have hq : 0 ≤ s⁻¹ * (star x ⬝ᵥ ((B - A) *ᵥ x)) := by
        simpa only [K, Matrix.mul_smul, trace_smul,
          trace_mul_vecMulVec_self_star, smul_eq_mul] using htrace
      have hsq := mul_nonneg hs.le hq
      simpa only [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] using hsq

/-- A positive operator is dominated by a nonnegative multiple of another
exactly when every measurement effect satisfies the corresponding Born-weight
inequality. The traces use the native partial order on complex scalars. -/
theorem le_smul_iff_born_le_effects {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (c : ℝ) (hc : 0 ≤ c) :
    ρ ≤ c • σ ↔ ∀ E : Matrix n n ℂ, 0 ≤ E ∧ E ≤ 1 →
      trace (E * ρ) ≤ (c : ℂ) * trace (E * σ) := by
  simpa only [Matrix.smul_mul, trace_smul, Complex.real_smul, trace_mul_comm] using
    (le_iff_trace_mul_le_effects hρ.isHermitian (hσ.smul hc).isHermitian)

end InfoGeometry.Quantum.PositiveEffectOrder
