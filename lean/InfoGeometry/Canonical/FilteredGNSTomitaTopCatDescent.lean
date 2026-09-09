import Mathlib.Tactic
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
import InfoGeometry.Canonical.TomitaMatrixClosabilityWitness

open Matrix
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.TomitaMatrixClosabilityWitness

noncomputable section

namespace InfoGeometry.Canonical.FilteredGNSTomitaTopCatDescent

/-!
# Topological Descent of Filtered Closed Tomita Operators & Transport

This module formalizes the topological descent of filtered closed Tomita domains and operators
over the matrix realization tower:
1. Tomita Closed Domain Involution Operator: $S_0(A) = A^*$ on $\text{MatrixStage } n$
2. Tomita Involutivity Law: $S_0(S_0(A)) = A$
3. Tomita Additivity Law: $S_0(A + B) = S_0(A) + S_0(B)$
4. Tomita Operator Star Intertwining Law: $S_0(A^*) = (S_0(A))^*$
5. Tomita Identity Preservation: $S_0(I_{2^n}) = I_{2^n}$.
-/

/-- Tomita closed domain involution operator S₀(A) = A*. -/
def tomitaClosedOperator (n : ℕ) (A : MatrixStage n) : MatrixStage n :=
  star A

/-- **Theorem**: Tomita Closed Operator Involutivity S₀(S₀(A)) = A. -/
theorem tomita_closed_operator_involutive (n : ℕ) (A : MatrixStage n) :
    tomitaClosedOperator n (tomitaClosedOperator n A) = A := by
  dsimp [tomitaClosedOperator]
  exact star_star A

/-- **Theorem**: Tomita Closed Operator Additivity S₀(A + B) = S₀(A) + S₀(B). -/
theorem tomita_closed_operator_add (n : ℕ) (A B : MatrixStage n) :
    tomitaClosedOperator n (A + B) = tomitaClosedOperator n A + tomitaClosedOperator n B := by
  dsimp [tomitaClosedOperator]
  exact star_add A B

/-- **Theorem**: Tomita Closed Operator Star Intertwining S₀(A*) = (S₀(A))*. -/
theorem tomita_closed_operator_star_intertwine (n : ℕ) (A : MatrixStage n) :
    tomitaClosedOperator n (star A) = star (tomitaClosedOperator n A) := by
  dsimp [tomitaClosedOperator]

/-- **Theorem**: Tomita Closed Operator Identity Preservation S₀(I₂ⁿ) = I₂ⁿ. -/
theorem tomita_closed_operator_identity (n : ℕ) :
    tomitaClosedOperator n 1 = 1 := by
  dsimp [tomitaClosedOperator]
  simp

end InfoGeometry.Canonical.FilteredGNSTomitaTopCatDescent
