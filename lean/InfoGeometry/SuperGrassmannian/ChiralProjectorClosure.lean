/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.CategoricalModuleColimitSato

namespace InfoGeometry.SuperGrassmannian.ModuleColimitSato

/-- The positive chiral projector is idempotent. -/
theorem projPlus_idempotent_closure {V : Type} [AddCommGroup V] [Module ℝ V]
    (G : LinearChiralGrading V) (v : V) :
    projPlus G (projPlus G v) = projPlus G v := by
  dsimp [projPlus]
  rw [G.map_smul, G.map_add, G.involutive]
  module

/-- The negative chiral projector is idempotent. -/
theorem projMinus_idempotent_closure {V : Type} [AddCommGroup V] [Module ℝ V]
    (G : LinearChiralGrading V) (v : V) :
    projMinus G (projMinus G v) = projMinus G v := by
  dsimp [projMinus]
  have hsub (x y : V) : G.gamma (x - y) = G.gamma x - G.gamma y := by
    rw [sub_eq_add_neg, G.map_add]
    have hneg : G.gamma (-y) = -G.gamma y := by
      rw [← neg_one_smul ℝ y, G.map_smul, neg_one_smul]
    rw [hneg, sub_eq_add_neg]
  rw [G.map_smul, hsub, G.involutive]
  module

/-- The two chiral projectors are mutually annihilating. -/
theorem projPlus_projMinus_closure {V : Type} [AddCommGroup V] [Module ℝ V]
    (G : LinearChiralGrading V) (v : V) :
    projPlus G (projMinus G v) = 0 := by
  dsimp [projPlus, projMinus]
  have hsub (x y : V) : G.gamma (x - y) = G.gamma x - G.gamma y := by
    rw [sub_eq_add_neg, G.map_add]
    have hneg : G.gamma (-y) = -G.gamma y := by
      rw [← neg_one_smul ℝ y, G.map_smul, neg_one_smul]
    rw [hneg, sub_eq_add_neg]
  rw [G.map_smul, hsub, G.involutive]
  module

/-- The two chiral projectors annihilate in the opposite order. -/
theorem projMinus_projPlus_closure {V : Type} [AddCommGroup V] [Module ℝ V]
    (G : LinearChiralGrading V) (v : V) :
    projMinus G (projPlus G v) = 0 := by
  dsimp [projMinus, projPlus]
  rw [G.map_smul, G.map_add, G.involutive]
  module

end InfoGeometry.SuperGrassmannian.ModuleColimitSato
