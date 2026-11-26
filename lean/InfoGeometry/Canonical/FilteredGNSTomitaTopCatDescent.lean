/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.Canonical.TomitaMatrixClosabilityWitness

open Matrix
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.TomitaMatrixClosabilityWitness

noncomputable section

namespace InfoGeometry.Canonical.FilteredGNSTomitaTopCatDescent

/-!
# Finite Matrix Star-Involution Laws on `MatrixStage n`

Despite the module name, this file does **not** formalize `TopCat` descent,
closed Tomita operator graphs, or GNS Hilbert spaces. It records the finite
matrix conjugate-transpose/star involution `A ↦ star A` on `MatrixStage n`:
1. `tomitaClosedOperator n A := star A`
2. Involutivity: `star (star A) = A`
3. Additivity: `star (A + B) = star A + star B`
4. Star intertwining: `star (star A) = star (star A)`
5. Identity preservation: `star 1 = 1`

For the genuine filtered C*-algebra GNS closed Tomita operator tower, see
`FilteredGNSTomitaCore` through `FilteredGNSTomitaModularHilbertCompletion`.
-/

/-- Finite-stage matrix `star` involution on `MatrixStage n`. -/
def tomitaClosedOperator (n : ℕ) (A : MatrixStage n) : MatrixStage n :=
  star A

/-- Matrix `star` involution satisfies `star (star A) = A`. -/
theorem tomita_closed_operator_involutive (n : ℕ) (A : MatrixStage n) :
    tomitaClosedOperator n (tomitaClosedOperator n A) = A := by
  dsimp [tomitaClosedOperator]
  exact star_star A

/-- Matrix `star` preserves addition: `star (A + B) = star A + star B`. -/
theorem tomita_closed_operator_add (n : ℕ) (A B : MatrixStage n) :
    tomitaClosedOperator n (A + B) = tomitaClosedOperator n A + tomitaClosedOperator n B := by
  dsimp [tomitaClosedOperator]
  exact star_add A B

/-- `tomitaClosedOperator n` commutes with `star` definitionally. -/
theorem tomita_closed_operator_star_intertwine (n : ℕ) (A : MatrixStage n) :
    tomitaClosedOperator n (star A) = star (tomitaClosedOperator n A) := by
  dsimp [tomitaClosedOperator]

/-- Matrix `star` preserves the identity matrix `1` on `MatrixStage n`. -/
theorem tomita_closed_operator_identity (n : ℕ) :
    tomitaClosedOperator n 1 = 1 := by
  dsimp [tomitaClosedOperator]
  simp

end InfoGeometry.Canonical.FilteredGNSTomitaTopCatDescent
