import InfoGeometry.Canonical.ThreeColorFixedCoreSuperLie

/-!
# Fixed-colour matrix core inside the native operator-valued Zorn carrier

The fixed-colour associative core is represented by `BdGBlock A`.  This file
embeds it into the native operator-valued Zorn coordinates and proves the
actual multiplication compatibility.  No associative or Lie structure is
installed on the full native carrier.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics
open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A] [Algebra ℝ A]

def fixedColourEmbedding (k : Fin 3) (X : FixedColourCore A) :
    OperatorZornMatrix A :=
  ⟨X 0 0, X 1 1,
    operatorColourUnit k (X 0 1),
    operatorColourUnit k (X 1 0)⟩

@[simp] theorem operatorColourUnit_cross_same (k : Fin 3) (a b : A) :
    operatorCross (operatorColourUnit k a)
        (operatorColourUnit k b) = 0 := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [operatorCross, operatorColourUnit,
      NCZornElement.zornCross]

@[simp] theorem fixedColourEmbedding_zero (k : Fin 3) :
    fixedColourEmbedding k (0 : FixedColourCore A) = 0 := by
  apply operatorZornMatrix_ext
  · rfl
  · rfl
  · funext i
    change (if i = k then (0 : A) else 0) = 0
    simp
  · funext i
    change (if i = k then (0 : A) else 0) = 0
    simp

private theorem if_mul_add_mul_same (p : Prop) [Decidable p]
    (a b c d : A) :
    (if p then a * b + c * d else 0) =
      (if p then a * b else 0) + (if p then c * d else 0) := by
  by_cases hp : p <;> simp [hp]

private theorem if_mul_add_mul_swapped (p : Prop) [Decidable p]
    (a b c d : A) :
    (if p then a * b + c * d else 0) =
      (if p then c * d else 0) + (if p then a * b else 0) := by
  by_cases hp : p <;> simp [hp, add_comm]

theorem fixedColourEmbedding_mul (k : Fin 3) (X Y : FixedColourCore A) :
    fixedColourEmbedding k (X * Y) =
      operatorZornMul (fixedColourEmbedding k X)
        (fixedColourEmbedding k Y) := by
  apply operatorZornMatrix_ext
  · simp [fixedColourEmbedding, operatorZornMul, NCZornElement.mul,
      Matrix.mul_apply, Fin.sum_univ_two,
      operatorDot_colourUnit_same]
  · simp [fixedColourEmbedding, operatorZornMul, NCZornElement.mul,
      Matrix.mul_apply, Fin.sum_univ_two,
      operatorDot_colourUnit_same]
    <;> abel
  · funext i
    fin_cases i
    all_goals
      simp [fixedColourEmbedding, operatorZornMul, NCZornElement.mul,
        operatorCross, operatorColourUnit, Matrix.mul_apply,
        Fin.sum_univ_two]
      <;> apply if_mul_add_mul_same
  · funext i
    fin_cases i
    all_goals
      simp [fixedColourEmbedding, operatorZornMul, NCZornElement.mul,
        operatorCross, operatorColourUnit, Matrix.mul_apply,
        Fin.sum_univ_two]
      <;> apply if_mul_add_mul_swapped

end InfoGeometry.Canonical
