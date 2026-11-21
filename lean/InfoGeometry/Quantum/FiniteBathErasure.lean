/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.MatrixTensorRank
import InfoGeometry.Quantum.MatrixBoundaryPurification
import InfoGeometry.Quantum.FinitePartialTrace

/-!
# A rank obstruction to exact erasure with a faithful finite bath

## Overview

All states are full complex matrices. A positive joint operator whose actual
second-factor partial trace is a star projection is supported on that
projection tensored with the bath identity. Tensor rank multiplication and
unitary rank invariance then prevent a system of rank greater than one from
acquiring a pure marginal when its initially uncorrelated finite bath is
positive and invertible.

The bath may be the existing normalized matrix CFC Gibbs density for any real
parameter. The proof does not restrict matrices to diagonal or commuting
families. Trace normalization of the initial operators is unnecessary for
this stronger algebraic obstruction.

## Key results

- `support_of_partialTrace_eq_projection`: both ordered support identities.
- `rank_le_of_partialTrace_eq_projection`: the corresponding support-rank bound.
- `no_pure_marginal_of_faithful_bath`: exact erasure obstruction for an arbitrary
  normalized target vector, not only a distinguished basis vector.
- `no_pure_marginal_of_normalizedGibbs_bath`: the existing Gibbs-state consumer.

## Table of contents

1. Unitary rank and positive-matrix support.
2. Partial-trace support and rank.
3. Faithful finite baths and the normalized Gibbs specialization.

## References

The native matrix positivity, Kronecker product, unitary group, partial trace,
and CFC Gibbs owners supply the operations. This finite-dimensional obstruction
does not assert that every other resource must diverge, and it does not apply
to a pure auxiliary bath.
-/

noncomputable section

namespace InfoGeometry.Quantum.FiniteBathErasure

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker
open InfoGeometry.Quantum.MatrixTensorRank
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open InfoGeometry.Quantum.MatrixBoundaryPurification
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.QuantumContext.MatrixStagePartialTrace

/-- Full matrix rank is invariant under the actual unitary conjugation. -/
theorem rank_unitary_conjugate {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ)).rank = A.rank := by
  have hU : IsUnit (U : Matrix n n ℂ) := Unitary.isUnit_coe
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _
      ((Matrix.isUnit_iff_isUnit_det _).mp hU.star),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _
      ((Matrix.isUnit_iff_isUnit_det _).mp hU)]

/-- Zero trace against a star projection annihilates the corresponding rows of
a positive matrix. Positivity supplies the Gram factor, rather than an assumed
support or product-state decomposition. -/
theorem projection_mul_eq_zero_of_trace_mul_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (A P : Matrix n n ℂ) (hA : A.PosSemidef) (hP : IsStarProjection P)
    (ht : Matrix.trace (P * A) = 0) : P * A = 0 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hgram : Matrix.trace (star (B * P) * (B * P)) = 0 := by
    calc
      Matrix.trace (star (B * P) * (B * P)) = Matrix.trace (P * A * P) := by
        rw [hB]
        simp only [star_mul, hP.isSelfAdjoint.star_eq, mul_assoc]
      _ = Matrix.trace (P * P * A) := Matrix.trace_mul_cycle P A P
      _ = 0 := by rw [hP.isIdempotentElem.eq, ht]
  have hBP : B * P = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hgram
  calc
    P * A = star (B * P) * B := by
      rw [hB]
      simp only [star_mul, hP.isSelfAdjoint.star_eq, mul_assoc]
    _ = 0 := by rw [hBP, star_zero, zero_mul]

/-- A projection-valued marginal forces both ordered support identities on the
full bipartite matrix. No product-state factorization is assumed. -/
theorem support_of_partialTrace_eq_projection {m n : ℕ}
    (σ : BipartiteOperator m n) (hσ : σ.PosSemidef)
    (P : Matrix (Fin m) (Fin m) ℂ) (hP : IsStarProjection P)
    (hmarg : partialTraceSecondOp σ = P) :
    (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * σ = σ ∧
      σ * (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) = σ := by
  have hPt : IsStarProjection (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    refine ⟨?_, ?_⟩
    · change (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * (P ⊗ₖ 1) = P ⊗ₖ 1
      rw [← Matrix.mul_kronecker_mul, hP.isIdempotentElem.eq, one_mul]
    · change (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = P ⊗ₖ 1
      rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
      exact congrArg (fun Q : Matrix (Fin m) (Fin m) ℂ =>
        Q ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) hP.isSelfAdjoint.star_eq
  have hcomp : (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
      1 - (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    calc
      (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) =
          (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
            P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
        ext ⟨i, j⟩ ⟨k, l⟩
        simp only [Matrix.kronecker_apply, Matrix.sub_apply, sub_mul]
      _ = _ := by rw [Matrix.one_kronecker_one]
  have ht : Matrix.trace ((1 - (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))) * σ) = 0 := by
    rw [← hcomp, ← trace_mul_partialTraceSecondOp (1 - P) σ,
      hmarg, hP.one_sub_mul_self, Matrix.trace_zero]
  have hz := projection_mul_eq_zero_of_trace_mul_eq_zero σ
    (1 - (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))) hσ hPt.one_sub ht
  have hleft : (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * σ = σ := by
    have hsub : σ - (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * σ = 0 := by
      simpa only [sub_mul, one_mul] using hz
    exact (sub_eq_zero.mp hsub).symm
  refine ⟨hleft, ?_⟩
  simpa only [star_mul, hσ.isHermitian.star_eq, hPt.isSelfAdjoint.star_eq] using
    congrArg star hleft

/-- The rank bound is derived from the actual support identity and native
matrix multiplication, before any purity specialization. -/
theorem rank_le_of_partialTrace_eq_projection {m n : ℕ}
    (σ : BipartiteOperator m n) (hσ : σ.PosSemidef)
    (P : Matrix (Fin m) (Fin m) ℂ) (hP : IsStarProjection P)
    (hmarg : partialTraceSecondOp σ = P) : σ.rank ≤ P.rank * n := by
  have hsupport := (support_of_partialTrace_eq_projection σ hσ P hP hmarg).1
  calc
    σ.rank = ((P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * σ).rank :=
      congrArg Matrix.rank hsupport.symm
    _ ≤ (P ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)).rank := Matrix.rank_mul_le_left _ _
    _ = P.rank * n := by rw [rank_kronecker, Matrix.rank_one, Fintype.card_fin]

/-- A mixed system and an initially uncorrelated faithful finite positive bath
cannot evolve unitarily to an arbitrary prescribed pure system state. -/
theorem no_pure_marginal_of_faithful_bath {m n : ℕ} [Nonempty (Fin n)]
    (ρ : Matrix (Fin m) (Fin m) ℂ) (γ : Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ.PosSemidef) (hγ : γ.PosSemidef) (hfaithful : IsUnit γ)
    (hmixed : 1 < ρ.rank) (U : unitary (BipartiteOperator m n))
    (v : Fin m → ℂ) (hv : star v ⬝ᵥ v = 1) :
    partialTraceSecondOp ((U : BipartiteOperator m n) * (ρ ⊗ₖ γ) *
      star (U : BipartiteOperator m n)) ≠ Matrix.vecMulVec v (star v) := by
  intro hmarg
  have hP : IsStarProjection (Matrix.vecMulVec v (star v)) := by
    refine ⟨?_, (Matrix.posSemidef_vecMulVec_self_star v).isHermitian⟩
    change Matrix.vecMulVec v (star v) * Matrix.vecMulVec v (star v) = _
    rw [Matrix.vecMulVec_mul_vecMulVec, hv, one_smul]
  have hσ := (hρ.kronecker hγ).mul_mul_conjTranspose_same (U : BipartiteOperator m n)
  have hbound := rank_le_of_partialTrace_eq_projection
    ((U : BipartiteOperator m n) * (ρ ⊗ₖ γ) * star (U : BipartiteOperator m n))
    hσ (Matrix.vecMulVec v (star v)) hP hmarg
  have hsmall : ρ.rank * n ≤ n := by
    have h := hbound.trans (Nat.mul_le_mul_right n (Matrix.rank_vecMulVec_le v (star v)))
    simpa only [rank_unitary_conjugate, rank_kronecker,
      Matrix.rank_of_isUnit γ hfaithful, Fintype.card_fin, one_mul] using h
  have hn : 0 < n := by simpa only [Fintype.card_fin] using Fintype.card_pos (α := Fin n)
  have hlarge : n < ρ.rank * n := by
    simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hmixed hn
  exact (not_le_of_gt hlarge) hsmall

/-- The existing normalized CFC Gibbs state is invertible, including its actual
nonzero partition normalization. -/
theorem normalizedGibbs_isUnit {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (β : ℝ) :
    IsUnit (normalizedGibbs H hH β) := by
  have hc : IsUnit ((Matrix.trace (gibbsDensity H hH β))⁻¹) :=
    isUnit_iff_ne_zero.mpr (inv_ne_zero (gibbsPartition_ne_zero H hH β))
  have hs : IsUnit ((Matrix.trace (gibbsDensity H hH β))⁻¹ • (1 : Matrix n n ℂ)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hc.map (algebraMap ℂ (Matrix n n ℂ))
  have hprod := hs.mul (gibbsDensity_isUnit H hH β)
  simpa only [normalizedGibbs, smul_mul_assoc, one_mul] using hprod

/-- The finite-bath obstruction applies to the preexisting normalized matrix
Gibbs state for every finite real parameter, without a spectral-diagonal model. -/
theorem no_pure_marginal_of_normalizedGibbs_bath {m n : ℕ} [Nonempty (Fin n)]
    (ρ : Matrix (Fin m) (Fin m) ℂ) (hρ : ρ.PosSemidef) (hmixed : 1 < ρ.rank)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (β : ℝ)
    (U : unitary (BipartiteOperator m n)) (v : Fin m → ℂ) (hv : star v ⬝ᵥ v = 1) :
    partialTraceSecondOp ((U : BipartiteOperator m n) *
      (ρ ⊗ₖ normalizedGibbs H hH β) * star (U : BipartiteOperator m n)) ≠
        Matrix.vecMulVec v (star v) :=
  no_pure_marginal_of_faithful_bath ρ (normalizedGibbs H hH β) hρ
    (normalizedGibbs_posSemidef H hH β) (normalizedGibbs_isUnit H hH β)
    hmixed U v hv

end InfoGeometry.Quantum.FiniteBathErasure
