import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.Canonical.CuntzStarInductiveSystem
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.Canonical.ConcreteCuntzMatrixIsometries
import InfoGeometry.Canonical.FiniteMatrixCuntzObstruction

open Matrix
open CStarStateColimit.Native
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.ConcreteCuntzMatrixIsometries
open InfoGeometry.Canonical.FiniteMatrixCuntzObstruction

noncomputable section

namespace InfoGeometry.Canonical.MatrixCuntzStarTower

/-!
# Concrete Matrix Cuntz Star Tower & Trace Obstruction

This module provides the concrete structure for the matrix UHF stage tower
`MatrixStage n := Matrix (Fin (2^n)) (Fin (2^n)) ℂ` with identity embeddings
and records the exact trace obstruction theorem for finite matrix stages:
1. **Identity Law**: `matrixEmbedId n = StarAlgHom.id ℂ (MatrixStage n)`
2. **Finite Stage Obstruction**: No non-zero finite matrix stage `Matrix (Fin n) (Fin n) ℂ` (n > 0)
   can hold a stagewise `Cuntz2Isometries` family, because `2n = n → False`.
-/

/-- Stage n of the matrix UHF tower: 2ⁿ × 2ⁿ complex matrix algebra. -/
abbrev MatrixStage (n : ℕ) : Type := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

/-- Identity embedding for same stage (used for the identity law). -/
def matrixEmbedId (n : ℕ) : MatrixStage n →⋆ₐ[ℂ] MatrixStage n :=
  StarAlgHom.id ℂ (MatrixStage n)

/-- **Theorem**: Identity Law — The identity embedding at stage n is the identity map. -/
theorem matrixEmbedId_law (n : ℕ) : matrixEmbedId n = StarAlgHom.id ℂ (MatrixStage n) := by
  rfl

/-- **Theorem**: Obstruction to Stagewise Cuntz Family at Finite Matrix Stages:
    No finite matrix stage MatrixStage n (n > 0) can hold a stagewise Cuntz O₂ family. -/
theorem matrixStage_cuntz_obstruction {n : ℕ} (hn : 0 < n)
    (C : CuntzAlgebra.Cuntz2Isometries (Matrix (Fin n) (Fin n) ℂ)) : False := by
  exact no_cuntz2_matrix hn C

end InfoGeometry.Canonical.MatrixCuntzStarTower