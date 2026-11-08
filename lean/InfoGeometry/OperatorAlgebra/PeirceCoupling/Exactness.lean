/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCoupling.GramGeometry
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exactness and the adjoint common kernel

The native matrix action on `EuclideanSpace ℂ n` identifies conjugate
transpose with the Hilbert-space adjoint. Orthogonal range/kernel geometry
then identifies a trivial common kernel with the sum of the two ranges being
the whole space. For a square-zero matrix, the same condition is exactness:
its range equals its kernel. Positive definiteness of the Gram sum therefore
forces twice the matrix rank to equal the dimension of the ambient space.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A square-zero matrix and its adjoint have no cancellation in their Hermitian sum. -/
theorem squareZero_sum_mulVec_eq_zero_iff (N : Matrix n n ℂ) (hN : N * N = 0)
    (v : n → ℂ) :
    (N + Nᴴ) *ᵥ v = 0 ↔ N *ᵥ v = 0 ∧ Nᴴ *ᵥ v = 0 := by
  constructor
  · intro hv
    have hprod := congrArg (fun w => N *ᵥ w) hv
    rw [mulVec_mulVec, mul_add, hN, zero_add, mulVec_zero] at hprod
    have hv' := (self_mul_conjTranspose_mulVec_eq_zero N v).mp hprod
    rw [add_mulVec, hv', add_zero] at hv
    exact ⟨hv, hv'⟩
  · rintro ⟨hv, hv'⟩
    rw [add_mulVec, hv, hv', add_zero]

theorem squareZero_sum_ker (N : Matrix n n ℂ) (hN : N * N = 0) :
    LinearMap.ker (N + Nᴴ).mulVecLin =
      LinearMap.ker N.mulVecLin ⊓ LinearMap.ker Nᴴ.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_inf,
    squareZero_sum_mulVec_eq_zero_iff N hN]

/-- Positive definiteness of the Gram sum is invertibility of the Hermitian sum. -/
theorem gramSum_posDef_iff_sum_isUnit (N : Matrix n n ℂ) (hN : N * N = 0) :
    (N * Nᴴ + Nᴴ * N).PosDef ↔ IsUnit (N + Nᴴ) := by
  rw [gramSum_posDef_iff_ker_inf_eq_bot, ← squareZero_sum_ker N hN,
    LinearMap.ker_eq_bot]
  change Function.Injective (N + Nᴴ).mulVec ↔ IsUnit (N + Nᴴ)
  exact Matrix.mulVec_injective_iff_isUnit

/-- The common-kernel identity transported through the native Euclidean realization. -/
theorem gramSum_euclidean_ker (N : Matrix n n ℂ) :
    LinearMap.ker (N * Nᴴ + Nᴴ * N).toEuclideanLin =
      LinearMap.ker N.toEuclideanLin ⊓ LinearMap.ker Nᴴ.toEuclideanLin := by
  ext v
  change WithLp.toLp 2 ((N * Nᴴ + Nᴴ * N) *ᵥ WithLp.ofLp v) = 0 ↔
    WithLp.toLp 2 (N *ᵥ WithLp.ofLp v) = 0 ∧
      WithLp.toLp 2 (Nᴴ *ᵥ WithLp.ofLp v) = 0
  simp only [WithLp.toLp_eq_zero, gramSum_mulVec_eq_zero_iff]

/-- Positive definiteness expressed in the Hilbert-space kernel lattice. -/
theorem gramSum_posDef_iff_euclidean_ker_inf_eq_bot (N : Matrix n n ℂ) :
    (N * Nᴴ + Nᴴ * N).PosDef ↔
      LinearMap.ker N.toEuclideanLin ⊓ LinearMap.ker Nᴴ.toEuclideanLin = ⊥ := by
  rw [gramSum_posDef_iff, Submodule.eq_bot_iff]
  constructor
  · intro h v hv
    change WithLp.toLp 2 (N *ᵥ WithLp.ofLp v) = 0 ∧
      WithLp.toLp 2 (Nᴴ *ᵥ WithLp.ofLp v) = 0 at hv
    apply (WithLp.ofLp_eq_zero 2).mp
    exact h (WithLp.ofLp v) ⟨(WithLp.toLp_eq_zero 2).mp hv.1,
      (WithLp.toLp_eq_zero 2).mp hv.2⟩
  · intro h v hv
    apply (WithLp.toLp_eq_zero 2).mp
    apply h (WithLp.toLp 2 v)
    change WithLp.toLp 2 (N *ᵥ v) = 0 ∧ WithLp.toLp 2 (Nᴴ *ᵥ v) = 0
    exact ⟨(WithLp.toLp_eq_zero 2).mpr hv.1, (WithLp.toLp_eq_zero 2).mpr hv.2⟩

/-- The two ranges span the full Euclidean space exactly when the common kernel is zero. -/
theorem euclidean_ker_inf_eq_bot_iff_range_sup_eq_top (N : Matrix n n ℂ) :
    LinearMap.ker N.toEuclideanLin ⊓ LinearMap.ker Nᴴ.toEuclideanLin = ⊥ ↔
      LinearMap.range N.toEuclideanLin ⊔ LinearMap.range Nᴴ.toEuclideanLin = ⊤ := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  let L := N.toEuclideanLin
  change L.ker ⊓ L.adjoint.ker = ⊥ ↔ L.range ⊔ L.adjoint.range = ⊤
  let : CompleteSpace ↥(L.range ⊔ L.adjoint.range) :=
    FiniteDimensional.complete ℂ _
  have horth : (L.range ⊔ L.adjoint.range)ᗮ = L.ker ⊓ L.adjoint.ker := by
    rw [← Submodule.inf_orthogonal, LinearMap.orthogonal_range,
      LinearMap.orthogonal_range, LinearMap.adjoint_adjoint, inf_comm]
  rw [← horth]
  exact Submodule.orthogonal_eq_bot_iff

/-- An unconditional range criterion for positive definiteness of the Gram sum. -/
theorem gramSum_posDef_iff_range_sup_eq_top (N : Matrix n n ℂ) :
    (N * Nᴴ + Nᴴ * N).PosDef ↔
      LinearMap.range N.toEuclideanLin ⊔ LinearMap.range Nᴴ.toEuclideanLin = ⊤ :=
  (gramSum_posDef_iff_euclidean_ker_inf_eq_bot N).trans
    (euclidean_ker_inf_eq_bot_iff_range_sup_eq_top N)

/-- Square-zero matrices give the native range-to-kernel inclusion. -/
theorem squareZero_euclidean_range_le_ker (N : Matrix n n ℂ) (hN : N * N = 0) :
    LinearMap.range N.toEuclideanLin ≤ LinearMap.ker N.toEuclideanLin := by
  apply LinearMap.range_le_ker_iff.mpr
  change Matrix.toLpLin 2 2 N ∘ₗ Matrix.toLpLin 2 2 N = 0
  rw [← Matrix.toLpLin_mul_same, hN, map_zero]

/-- For a square-zero matrix, the common kernel measures the failure of exactness. -/
theorem squareZero_ker_inf_eq_bot_iff_exact (N : Matrix n n ℂ) (hN : N * N = 0) :
    LinearMap.ker N.toEuclideanLin ⊓ LinearMap.ker Nᴴ.toEuclideanLin = ⊥ ↔
      LinearMap.range N.toEuclideanLin = LinearMap.ker N.toEuclideanLin := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  let L := N.toEuclideanLin
  change L.ker ⊓ L.adjoint.ker = ⊥ ↔ L.range = L.ker
  have hle : L.range ≤ L.ker := squareZero_euclidean_range_le_ker N hN
  let : CompleteSpace L.range := FiniteDimensional.complete ℂ _
  constructor
  · intro h
    have hdecomp := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
    rw [LinearMap.orthogonal_range, inf_comm, h, sup_bot_eq] at hdecomp
    exact hdecomp
  · intro h
    rw [← h, ← LinearMap.orthogonal_range]
    exact Submodule.inf_orthogonal_eq_bot L.range

/-- For a square-zero matrix, positive definiteness is equivalent to exactness. -/
theorem gramSum_posDef_iff_exact (N : Matrix n n ℂ) (hN : N * N = 0) :
    (N * Nᴴ + Nᴴ * N).PosDef ↔
      LinearMap.range N.toEuclideanLin = LinearMap.ker N.toEuclideanLin :=
  (gramSum_posDef_iff_euclidean_ker_inf_eq_bot N).trans
    (squareZero_ker_inf_eq_bot_iff_exact N hN)

/-- Rank-nullity makes the exact range half of the ambient dimension. -/
theorem card_eq_two_mul_finrank_range_of_gramSum_posDef (N : Matrix n n ℂ)
    (hN : N * N = 0) (hH : (N * Nᴴ + Nᴴ * N).PosDef) :
    Fintype.card n = 2 * Module.finrank ℂ (LinearMap.range N.toEuclideanLin) := by
  have hexact := (gramSum_posDef_iff_exact N hN).mp hH
  have hdim := LinearMap.finrank_range_add_finrank_ker N.toEuclideanLin
  rw [← hexact, ← two_mul, finrank_euclideanSpace] at hdim
  exact hdim.symm

/-- The same dimension constraint stated using the native matrix rank. -/
theorem card_eq_two_mul_rank_of_gramSum_posDef (N : Matrix n n ℂ)
    (hN : N * N = 0) (hH : (N * Nᴴ + Nᴴ * N).PosDef) :
    Fintype.card n = 2 * N.rank := by
  have hrank : N.rank = Module.finrank ℂ (LinearMap.range N.toEuclideanLin) :=
    N.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun n ℂ).toBasis
      (EuclideanSpace.basisFun n ℂ).toBasis
  rw [hrank]
  exact card_eq_two_mul_finrank_range_of_gramSum_posDef N hN hH

/-- A square-zero matrix with positive-definite Gram sum requires even ambient dimension. -/
theorem even_card_of_gramSum_posDef (N : Matrix n n ℂ)
    (hN : N * N = 0) (hH : (N * Nᴴ + Nᴴ * N).PosDef) :
    Even (Fintype.card n) := by
  refine ⟨N.rank, ?_⟩
  simpa only [two_mul] using card_eq_two_mul_rank_of_gramSum_posDef N hN hH

end InfoGeometry.OperatorAlgebra.PeirceCoupling
