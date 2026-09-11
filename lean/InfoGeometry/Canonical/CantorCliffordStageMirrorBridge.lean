import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ChiralBoundarySheetReflectionTopological

/-!
# Stage-to-boundary mirror bridge

The local sheet exchange is lifted through the existing binary tensor tower.
Only the induced inner automorphisms are compared with the standard stage
embedding; the implementing matrices themselves are not asserted to form a
compatible family.
-/

noncomputable section

open scoped Matrix Kronecker

namespace InfoGeometry.Canonical.CantorCliffordStageMirrorBridge

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.CantorCliffordFunctionModel
open InfoGeometry.Canonical.ChiralLightConeTensorTower

def localSheetExchange : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(0 : ℝ), 1; 1, 0]

@[simp] theorem localSheetExchange_sq :
    localSheetExchange * localSheetExchange = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [localSheetExchange, Matrix.mul_apply, Fin.sum_univ_two]

def stageSheetExchange (n : ℕ) : MatStage n :=
  TowerMatrix.kronPow localSheetExchange n

@[simp] theorem stageSheetExchange_sq (n : ℕ) :
    stageSheetExchange n * stageSheetExchange n = 1 := by
  exact TowerMatrix.Jn_sq localSheetExchange localSheetExchange_sq n

def stageMirrorAction (n : ℕ) (A : MatStage n) : MatStage n :=
  stageSheetExchange n * A * stageSheetExchange n

@[simp] theorem stageMirrorAction_one (n : ℕ) :
    stageMirrorAction n 1 = 1 := by
  simp [stageMirrorAction, stageSheetExchange_sq]

theorem stageMirrorAction_add (n : ℕ) (A B : MatStage n) :
    stageMirrorAction n (A + B) =
      stageMirrorAction n A + stageMirrorAction n B := by
  simp [stageMirrorAction, mul_add, add_mul]

theorem stageMirrorAction_mul (n : ℕ) (A B : MatStage n) :
    stageMirrorAction n (A * B) =
      stageMirrorAction n A * stageMirrorAction n B := by
  let J := stageSheetExchange n
  have hJ : J * J = (1 : MatStage n) := by
    exact stageSheetExchange_sq n
  change J * (A * B) * J = (J * A * J) * (J * B * J)
  calc
    J * (A * B) * J = J * A * B * J := by simp [Matrix.mul_assoc]
    _ = J * A * (J * J) * B * J := by simp [hJ, Matrix.mul_assoc]
    _ = (J * A * J) * (J * B * J) := by simp [Matrix.mul_assoc]

@[simp] theorem stageMirrorAction_involutive (n : ℕ) (A : MatStage n) :
    stageMirrorAction n (stageMirrorAction n A) = A := by
  let J := stageSheetExchange n
  have hJ : J * J = (1 : MatStage n) := by
    exact stageSheetExchange_sq n
  change J * (J * A * J) * J = A
  calc
    J * (J * A * J) * J = (J * J) * A * (J * J) := by
      simp [Matrix.mul_assoc]
    _ = A := by simp [hJ]

theorem stageSheetExchange_succ_eq_kron (n : ℕ) :
    stageSheetExchange (n + 1) =
      stageSheetExchange n ⊗ₖ localSheetExchange := by
  rfl

theorem stageMirrorAction_embed (n : ℕ) (A : MatStage n) :
    stageMirrorAction (n + 1) (matStageEmbed n A) =
      matStageEmbed n (stageMirrorAction n A) := by
  simp only [stageMirrorAction, matStageEmbed,
    stageSheetExchange_succ_eq_kron]
  rw [← Matrix.mul_kronecker_mul]
  rw [← Matrix.mul_kronecker_mul]
  simp [Matrix.mul_assoc, localSheetExchange_sq]

theorem prefixReadout_boundaryMirror
    (n : ℕ) (ξ : ChiralBoundary) :
    prefixReadout (n := n) (boundaryMirror ξ) =
      mirrorCausalWord (prefixReadout (n := n) ξ) := by
  funext k
  rfl

end InfoGeometry.Canonical.CantorCliffordStageMirrorBridge
