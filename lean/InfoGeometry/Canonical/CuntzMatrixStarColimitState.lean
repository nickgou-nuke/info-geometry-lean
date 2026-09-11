import InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit

/-!
# The finite positive state net for the concrete star-algebra tower

This file connects the concrete matrix tower with the existing algebraic GNS
state owner.  It deliberately does not identify the separately constructed
`DirectLimit` carrier with a Hilbert or C*-completion, and it does not invent a
functional on that carrier.  The available theorem is the precise finite-stage
state net together with its compatibility under the genuine noncommutative
matrix embeddings.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixStarColimitState

open InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Meta.MarkovJonesInduction
open InfoGeometry.Prequantum.AlgebraicGNSState

/-- The normalized real matrix-trace state net for the concrete tower. -/
def concreteStateNet :
    CompatibleAlgebraicStateNet (realInductiveNet concreteData) :=
compatibleRealStateNet concreteData

@[simp] theorem concreteStateNet_state (n : ℕ) (A : MatrixStage n) :
    (concreteStateNet.state n) A =
      (matrixTraceFunctional n A).re := by
  exact compatibleRealStateNet_state concreteData n A

theorem concreteStateNet_normalized (n : ℕ) :
    concreteStateNet.state n 1 = 1 := by
  exact concreteStateNet.normalized n

theorem concreteStateNet_positive (n : ℕ) (A : MatrixStage n) :
    0 ≤ concreteStateNet.state n (star A * A) := by
  exact concreteStateNet.positive n A

theorem concreteStateNet_stable (n : ℕ) (A : MatrixStage n) :
    concreteStateNet.state (n + 1) (concreteStep n A) =
      concreteStateNet.state n A := by
  exact concreteStateNet.stable_one_step n A

theorem concreteStateNet_stable_map
    {m n : ℕ} (hmn : m ≤ n) (A : MatrixStage m) :
    concreteStateNet.state n (concreteMap hmn A) =
      concreteStateNet.state m A := by
  have h_embed :
      (realInductiveNet concreteData).embedMap m n hmn A =
        concreteMap hmn A := by
    induction hmn with
    | refl =>
        rw [InductiveAlgebraNet.embedMap_refl]
        rw [concreteMap_id]
        rfl
    | @step n h ih =>
        rw [InductiveAlgebraNet.embedMap_succ]
        change concreteStep n
            ((realInductiveNet concreteData).embedMap m n h A) = _
        rw [ih]
        change concreteStep n (concreteMap h A) =
          map concreteData (Nat.le.step h) A
        rw [map_succ concreteData h]
        rfl
  rw [← h_embed]
  exact CompatibleAlgebraicStateNet.stable_embedMap
    concreteStateNet m n hmn A

end InfoGeometry.Canonical.CuntzMatrixStarColimitState
