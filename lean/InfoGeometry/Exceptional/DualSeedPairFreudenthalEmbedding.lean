/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Exceptional.DualSeedPairAlbertEmbedding
import InfoGeometry.Exceptional.Freudenthal
import InfoGeometry.Core.DualSeedPeirce
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Ring

/-!
# Gap 5: Dual Seed Pair → Freudenthal Cubic Jordan Datum

Proves the trace pairing and degree-2 vs. degree-3 cubic-norm dichotomy for the
embedding of the dual seed pair Peirce algebra into the 27-dimensional split
Albert algebra `H3Zorn ℝ` (`h3zornCubicJordanDatum : CubicJordanDatum (H3Zorn ℝ)`):
1. On the embedded Peirce idempotents `cuntzToAlbert_e1`, `cuntzToAlbert_e2`, and their
   Freudenthal cross-product complement `cuntzToAlbert_e3 = crossProduct cuntzToAlbert_e1 cuntzToAlbert_e2`,
   the canonical bilinear trace form `h3zornTraceBilin` has unit self-pairings (`= 1 ≠ 0`).
2. On the 3-parameter degree-2 spin factor `α • e₁ + β • e₂ + γ • Q₁`, the cubic norm
   `normCubic` vanishes identically (`= 0`), whereas adjoining the complementary third
   Peirce idempotent `δ • (e₁ × e₂)` yields the factored cubic determinant
   `normCubic (α • e₁ + β • e₂ + γ • Q₁ + δ • e₃) = δ * (α * β - γ ^ 2)`.
-/

noncomputable section

namespace InfoGeometry.Exceptional.DualSeedPairFreudenthal

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Exceptional.DualSeedPairAlbertEmbedding

/-- **1. Non-Zero Trace & Freudenthal Cross-Product Pairing on the Embedded Dual Seed Idempotents**:
    The canonical trace bilinear form `h3zornTraceBilin : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] ℝ`
    pairs each embedded Peirce idempotent `e₁, e₂` with itself to `1 ≠ 0` and pairs
    `e₁ × e₂` with the complementary third idempotent `e₃` to `1 ≠ 0`. -/
theorem dual_seed_pair_albert_trace_pairing :
    h3zornTraceBilin cuntzToAlbert_e1 cuntzToAlbert_e1 = 1 ∧
    h3zornTraceBilin cuntzToAlbert_e2 cuntzToAlbert_e2 = 1 ∧
    h3zornTraceBilin cuntzToAlbert_e3 (crossProduct cuntzToAlbert_e1 cuntzToAlbert_e2) = 1 ∧
    h3zornTraceBilin cuntzToAlbert_e3 (crossProduct cuntzToAlbert_e1 cuntzToAlbert_e2) ≠ 0 := by
  rw [crossProduct_e1_e2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change traceBilin cuntzToAlbert_e1 cuntzToAlbert_e1 = 1
    simp [traceBilin, cuntzToAlbert_e1, ZornVectorMatrix.trace_zero]
  · change traceBilin cuntzToAlbert_e2 cuntzToAlbert_e2 = 1
    simp [traceBilin, cuntzToAlbert_e2, ZornVectorMatrix.trace_zero]
  · change traceBilin cuntzToAlbert_e3 cuntzToAlbert_e3 = 1
    simp [traceBilin, cuntzToAlbert_e3, ZornVectorMatrix.trace_zero]
  · change traceBilin cuntzToAlbert_e3 cuntzToAlbert_e3 ≠ 0
    simp [traceBilin, cuntzToAlbert_e3, ZornVectorMatrix.trace_zero]

/-- **2. Degree-2 Spin-Factor Vanishing vs. Degree-3 Freudenthal Cubic Norm Restoration**:
    - On the 2×2 Peirce spin-factor span `α • e₁ + β • e₂ + γ • Q₁`, the cubic norm `normCubic`
      vanishes identically (`= 0`) because it is a degree-2 subalgebra (`δ = 0`).
    - Adjoining the complementary third idempotent `δ • (e₁ × e₂) = δ • e₃` restores the
      non-degenerate degree-3 cubic determinant `δ * (α * β - γ ^ 2)`. -/
theorem dual_seed_pair_degree_two_vs_degree_three_cubic_norm (α β γ δ : ℝ) :
    normCubic (α • cuntzToAlbert_e1 + β • cuntzToAlbert_e2 + γ • cuntzToAlbert_Q1) = 0 ∧
    normCubic (α • cuntzToAlbert_e1 + β • cuntzToAlbert_e2 + γ • cuntzToAlbert_Q1 +
               δ • crossProduct cuntzToAlbert_e1 cuntzToAlbert_e2) =
      δ * (α * β - γ ^ 2) := by
  refine ⟨normCubic_spin_factor_vanishes α β γ, ?_⟩
  rw [crossProduct_e1_e2]
  simp [normCubic, cuntzToAlbert_e1, cuntzToAlbert_e2, cuntzToAlbert_e3, cuntzToAlbert_Q1,
        ZornVectorMatrix.smul_zero, ZornVectorMatrix.add_zero, ZornVectorMatrix.zero_add,
        ZornVectorMatrix.norm_zero, ZornVectorMatrix.norm_smul, ZornVectorMatrix.norm_one,
        ZornVectorMatrix.trace_zero]
  ring

end InfoGeometry.Exceptional.DualSeedPairFreudenthal
