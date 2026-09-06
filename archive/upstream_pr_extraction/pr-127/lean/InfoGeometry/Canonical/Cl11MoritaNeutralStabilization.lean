import InfoGeometry.Clifford.Cl11TensorTower

namespace InfoGeometry.Canonical.Cl11MoritaNeutralStabilization

open InfoGeometry.Clifford

/-!
# Morita-neutral Clifford stabilization readout

This owner records only the associative matrix readout already supplied by
`TowerMatrix`.  It does not identify the stage with a composition algebra or
make any Bott-periodicity claim.
-/

abbrev StageThree := TowerMatrix.Mat 3

theorem stageThree_finPowTwo_eq_eight :
    (2 : ℕ) ^ 3 = 8 := by
  norm_num

theorem stageThree_index_card :
    Fintype.card (TowerMatrix.Idx 3) = 8 := by
  simpa using TowerMatrix.idx_card_pow_two 3

noncomputable def stageThreeMatrix8 :
    StageThree ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  TowerMatrix.matEquivFinPowTwo 3

@[simp] theorem stageThreeMatrix8_apply (A : StageThree) :
    stageThreeMatrix8 A = TowerMatrix.matEquivFinPowTwo 3 A :=
  rfl

theorem stageThreeMatrix8_mul (A B : StageThree) :
    stageThreeMatrix8 (A * B) =
      stageThreeMatrix8 A * stageThreeMatrix8 B := by
  exact stageThreeMatrix8.map_mul A B

theorem stageThreeMatrix8_one :
    stageThreeMatrix8 (1 : StageThree) = 1 := by
  exact stageThreeMatrix8.map_one

noncomputable def standardMatrixStageEmbed (n : ℕ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ →ₐ[ℝ]
      Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℝ :=
  (TowerMatrix.matEquivFinPowTwo (n + 1)).toAlgHom.comp
    ((Cl11TensorTower.stageEmbed n).comp
      (TowerMatrix.matEquivFinPowTwo n).symm.toAlgHom)

theorem standardMatrixStageEmbed_compatibility
    (n : ℕ) (A : TowerMatrix.Mat n) :
    standardMatrixStageEmbed n
        (TowerMatrix.matEquivFinPowTwo n A) =
      TowerMatrix.matEquivFinPowTwo (n + 1)
        (Cl11TensorTower.stageEmbed n A) := by
  simp [standardMatrixStageEmbed]

theorem stageTwo_to_stageThree_matrix_compatibility
    (A : TowerMatrix.Mat 2) :
    standardMatrixStageEmbed 2
        (TowerMatrix.matEquivFinPowTwo 2 A) =
      stageThreeMatrix8 (Cl11TensorTower.stageEmbed 2 A) := by
  exact standardMatrixStageEmbed_compatibility 2 A

noncomputable def stageTwoMatrix4Unit
    (u : (TowerMatrix.Mat 2)ˣ) :
    (Matrix (Fin 4) (Fin 4) ℝ)ˣ :=
  Units.map (TowerMatrix.matEquivFinPowTwo 2).toMonoidHom u

@[simp] theorem stageTwoMatrix4Unit_val
    (u : (TowerMatrix.Mat 2)ˣ) :
    (stageTwoMatrix4Unit u : Matrix (Fin 4) (Fin 4) ℝ) =
      TowerMatrix.matEquivFinPowTwo 2 (u : TowerMatrix.Mat 2) := by
  simp [stageTwoMatrix4Unit]

@[simp] theorem stageTwoMatrix4Unit_one :
    stageTwoMatrix4Unit (1 : (TowerMatrix.Mat 2)ˣ) = 1 := by
  simp [stageTwoMatrix4Unit]

@[simp] theorem stageTwoMatrix4Unit_mul
    (u v : (TowerMatrix.Mat 2)ˣ) :
    stageTwoMatrix4Unit (u * v) =
      stageTwoMatrix4Unit u * stageTwoMatrix4Unit v := by
  simp [stageTwoMatrix4Unit]

end InfoGeometry.Canonical.Cl11MoritaNeutralStabilization
