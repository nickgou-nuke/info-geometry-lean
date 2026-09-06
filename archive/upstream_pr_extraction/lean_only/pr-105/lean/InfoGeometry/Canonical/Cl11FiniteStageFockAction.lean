import InfoGeometry.Clifford.Cl11TensorTower

/-!
# Finite algebraic actions for the dyadic Clifford stages

This owner supplies only a finite algebraic representation.  It deliberately
does not introduce a normed Fock carrier, a completion, or a second colimit.
The filtered inductive and inverse-colimit descent is owned by the existing
categorical modules.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11FiniteStageFockAction

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix

abbrev StageSpace (n : ℕ) := Idx n → ℝ
abbrev StageDoubledSpace (n : ℕ) := StageSpace n × StageSpace n
abbrev StageOperator (n : ℕ) := Module.End ℝ (StageDoubledSpace n)

def matrixAction (n : ℕ) (A : MatStage n) :
    StageDoubledSpace n →ₗ[ℝ] StageDoubledSpace n where
  toFun u := (Matrix.mulVec A u.1, Matrix.mulVec A u.2)
  map_add' u v := by
    ext i <;> simp [Matrix.mulVec_add]
  map_smul' r u := by
    ext i <;> simp [Matrix.mulVec_smul]

@[simp] theorem matrixAction_apply (n : ℕ) (A : MatStage n)
    (x y : StageSpace n) :
    matrixAction n A (x, y) = (Matrix.mulVec A x, Matrix.mulVec A y) := by
  rfl

noncomputable def stageRepresentation (n : ℕ) :
  MatStage n →+* StageOperator n where
  toFun A := matrixAction n A
  map_one' := by
    apply LinearMap.ext
    intro u
    ext i <;> simp [matrixAction]
  map_mul' A B := by
    apply LinearMap.ext
    intro u
    ext i <;> simp [matrixAction, Matrix.mulVec_mulVec]
  map_zero' := by
    apply LinearMap.ext
    intro u
    ext i <;> simp [matrixAction]
  map_add' A B := by
    apply LinearMap.ext
    intro u
    change (Matrix.mulVec (A + B) u.1, Matrix.mulVec (A + B) u.2) =
      (Matrix.mulVec A u.1 + Matrix.mulVec B u.1,
        Matrix.mulVec A u.2 + Matrix.mulVec B u.2)
    ext i <;> simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib,
      add_mul]

@[simp] theorem stageRepresentation_apply (n : ℕ) (A : MatStage n)
    (u : StageDoubledSpace n) :
    stageRepresentation n A u = matrixAction n A u := rfl

theorem stageRepresentation_mul_apply (n : ℕ) (A B : MatStage n)
    (u : StageDoubledSpace n) :
    stageRepresentation n (A * B) u =
      stageRepresentation n A (stageRepresentation n B u) := by
  change matrixAction n (A * B) u = matrixAction n A (matrixAction n B u)
  ext i <;> simp [matrixAction, Matrix.mulVec_mulVec]

end InfoGeometry.Canonical.Cl11FiniteStageFockAction
