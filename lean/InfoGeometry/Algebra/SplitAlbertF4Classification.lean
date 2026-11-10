/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.H3ZornCarrierBasis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# Split-Albert Carrier Dimension and Exceptional Dimension Ledger

This module contains a dimension ledger and readouts for the split-Albert
carrier. The Albert carrier dimension is proved below from its actual
`H3Zorn ℝ` coordinate basis. The F₄/SO(8)/G₂ numbers are arithmetic
bookkeeping only: they do not establish dimensions of those Lie algebras, a
direct-sum decomposition, or graded projection maps. The native F₄ derivation
carrier and the conditional hypotheses needed for its exact dimension are
owned by `InfoGeometry.Exceptional.F4DerivationsAlbert` and
`InfoGeometry.Canonical.F4ActionSolderingBridge`.
-/

noncomputable section

namespace InfoGeometry.Algebra.F4Classification

open H3Zorn
open InfoGeometry.Algebra

/-!
=============================================================================
PART 1: The Actual Albert Carrier Dimension and Its Count Ledger
=============================================================================
-/

/-- The dimension of the real scalar diagonal center in H₃(𝕆_s). -/
def dimRealDiagonal : ℕ := 3

/-- The real dimension of the split-octonion algebra 𝕆_s. -/
def dimSplitOctonions : ℕ := 8

/-- The number of off-diagonal octonionic pairs in a 3×3 Hermitian matrix. -/
def numOffDiagonalSectors : ℕ := 3

/-- Natural-number count assembled from three diagonal and three 8-coordinate
Zorn blocks. The actual carrier finrank is `albert_dimension_eq_27`. -/
def dimAlbertAlgebra : ℕ := dimRealDiagonal + numOffDiagonalSectors * dimSplitOctonions

/-- Arithmetic check for the displayed decomposition count `3 + 3 * 8`. -/
theorem dimAlbertAlgebra_formula_eq_27 : dimAlbertAlgebra = 27 := by
  dsimp [dimAlbertAlgebra, dimRealDiagonal, numOffDiagonalSectors, dimSplitOctonions]

/-- The actual real carrier `H3Zorn ℝ` has finrank 27, by its explicit
coordinate equivalence with functions `Fin 27 → ℝ`. -/
theorem albert_dimension_eq_27 : Module.finrank ℝ (H3Zorn ℝ) = 27 :=
  InfoGeometry.Algebra.finrank_h3zorn

/-- 
  Linear embedding of the 27 coordinates (α₁, α₂, α₃, a, b, c) into H₃(𝕆_s).
-/
def albertCoordinateMap
    (α₁ α₂ α₃ : ℝ)
    (a b c : ZornVectorMatrix ℝ) : H3Zorn ℝ :=
  { α₁ := α₁, α₂ := α₂, α₃ := α₃, a := a, b := b, c := c }

@[simp]
theorem albertCoordinateMap_surjective (X : H3Zorn ℝ) :
    albertCoordinateMap X.α₁ X.α₂ X.α₃ X.a X.b X.c = X := by
  rfl

/-!
=============================================================================
PART 2: Expected F₄ Count Ledger (No Carrier Decomposition Here)
=============================================================================
-/

/-- Expected-count entry for the split-octonion derivation algebra. -/
def dimG2Derivations : ℕ := 14

/-- Expected-count entry for the orthogonal Lie algebra. -/
def dimSO8LieAlgebra : ℕ := 28

/-- Expected F₄ count from the arithmetic decomposition ledger. This is not
the finrank of the native derivation carrier. -/
def dimF4Derivations : ℕ := dimSO8LieAlgebra + numOffDiagonalSectors * dimSplitOctonions

/-- Arithmetic check of the expected count `28 + 3 * 8`; this is not an exact
dimension theorem for `H3ZornF4Derivations`. -/
theorem f4_derivation_count_formula_eq_52 : dimF4Derivations = 52 := by
  dsimp [dimF4Derivations, dimSO8LieAlgebra, numOffDiagonalSectors, dimSplitOctonions]

/-- Arithmetic check that the chosen SO(8) and three-sector ledger entries
sum to the expected F₄ count. This is not a direct-sum decomposition theorem. -/
theorem f4_triality_dimension_ledger_sum :
    dimSO8LieAlgebra + numOffDiagonalSectors * dimSplitOctonions = dimF4Derivations := by
  rfl

theorem so8_g2_dimension_ledger_sum :
    dimG2Derivations + 7 + 7 = dimSO8LieAlgebra := by
  rfl

/-!
=============================================================================
PART 3: Graded F₄ Derivation Generators and Lie Bracket Preservation
=============================================================================
-/

/-- The total number of explicit basis derivations in the F₄ basis. -/
def f4BasisCount : ℕ := 52

theorem f4Basis_card_eq : f4BasisCount = dimF4Derivations := by
  rfl

/- The explicit `f4Basis` carrier is not owned by this dimension-only module;
   its trace-level owner is separate.  The generator theorem is deferred until
   that carrier is imported here. -/

end InfoGeometry.Algebra.F4Classification

end noncomputable section
