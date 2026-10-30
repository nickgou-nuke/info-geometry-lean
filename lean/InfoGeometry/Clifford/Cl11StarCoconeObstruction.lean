/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11StarAlgebraColimit

/-!
# A faithful compatible cocone need not be a colimit

The diagonal family into the product of two copies of the actual noncommutative
real matrix limit is compatible and stagewise injective. Two distinct native
star-algebra projections agree on every stage image, obstructing uniqueness.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11StarCoconeObstruction

open Cl11TensorTower Cl11TensorTowerLimit Cl11StarAlgebraColimit

/-- Compatibility holds even though the diagonal family does not exhaust the product. -/
theorem diagonal_compatible (n : ℕ) (A : Stage n) :
    (ofStageStarAlgHom (n + 1)).prod (ofStageStarAlgHom (n + 1)) (stageEmbed n A) =
      (ofStageStarAlgHom n).prod (ofStageStarAlgHom n) A := by
  change (ofStage (n + 1) (stageEmbed n A), ofStage (n + 1) (stageEmbed n A)) =
    (ofStage n A, ofStage n A)
  rw [ofStage_apply_bond]

theorem diagonal_injective (n : ℕ) :
    Function.Injective ((ofStageStarAlgHom n).prod (ofStageStarAlgHom n)) := by
  intro A B h
  exact ofStage_injective n (congrArg Prod.fst h)

/-- The two projections are different maps between full real operator algebras. -/
theorem projections_ne :
    StarAlgHom.fst ℝ Limit Limit ≠ StarAlgHom.snd ℝ Limit Limit := by
  intro h
  have hunit := DFunLike.congr_fun h (1, 0)
  exact one_ne_zero hunit

/-- The compatible faithful product cocone fails the universal uniqueness property. -/
theorem diagonal_not_existsUnique :
    ¬ ∃! g : Limit × Limit →⋆ₐ[ℝ] Limit,
      ∀ n A, g (ofStage n A, ofStage n A) = ofStage n A := by
  rintro ⟨g, _, hg⟩
  have hfst := hg (StarAlgHom.fst ℝ Limit Limit) (fun _ _ => rfl)
  have hsnd := hg (StarAlgHom.snd ℝ Limit Limit) (fun _ _ => rfl)
  exact projections_ne (hfst.trans hsnd.symm)

end InfoGeometry.Clifford.Cl11StarCoconeObstruction
