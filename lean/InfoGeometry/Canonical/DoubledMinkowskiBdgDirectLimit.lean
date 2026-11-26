/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiConcreteTowerGap
import InfoGeometry.LinearAlgebra.CompatibleBilinearColimit

/-!
# Native algebraic direct limit of the concrete BdG tower

The iterated padding maps of `DoubledMinkowskiConcreteTowerGap` form a genuine
`DirectedSystem`. This module supplies the stage bilinear forms given by the
sheet-Krein pairing and descends them to the native Mathlib `DirectLimit`
carrier through `CompatibleBilinearColimit.form`.

This is an algebraic colimit of finite BdG state spaces with its inherited
indefinite pairing. It does not assert a continuum Yang–Mills manifold,
Wightman/OS axioms, completion, topology, or a physical spectral mass gap.
-/

noncomputable section

namespace InfoGeometry.Canonical.DoubledMinkowskiBdgDirectLimit

open InfoGeometry.Canonical.DoubledMinkowskiConcreteTowerGap
open InfoGeometry.LinearAlgebra.CompatibleBilinearColimit

/-- Sheet-Krein pairing as a native bilinear form on a finite BdG stage. -/
def bdgStageKreinBilin (n : ℕ) : LinearMap.BilinForm ℝ (BdgTowerState n) where
  toFun ψ :=
    { toFun := fun φ => bdgKreinPair ψ φ
      map_add' := by
        intro φ χ
        simp [bdgKreinPair, Matrix.mulVec_add, dotProduct_add]
      map_smul' := by
        intro a φ
        simp [bdgKreinPair, Matrix.mulVec_smul, dotProduct_smul] }
  map_add' := by
    intro ψ φ
    ext χ
    simp [bdgKreinPair, Matrix.dotProduct_mulVec, Matrix.add_vecMul, dotProduct_add]
  map_smul' := by
    intro a ψ
    ext χ
    simp [bdgKreinPair, Matrix.dotProduct_mulVec, Matrix.smul_vecMul, smul_dotProduct]

/-- The native bilinear form agrees with the finite-stage sheet-Krein pairing. -/
theorem bdgStageKreinBilin_apply (n : ℕ) (ψ φ : BdgTowerState n) :
    bdgStageKreinBilin n ψ φ = bdgKreinPair ψ φ := rfl

/-- Iterated padding preserves the sheet-Krein pairing. -/
theorem padFun_bdgKreinPair (i j : ℕ) (h : i ≤ j) (x y : BdgTowerState i) :
    bdgKreinPair (padFun i j h x) (padFun i j h y) = bdgKreinPair x y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  change bdgKreinPair (padFun i (i + d) (Nat.le_add_right i d) x)
      (padFun i (i + d) (Nat.le_add_right i d) y) = bdgKreinPair x y
  induction d with
  | zero => simp [padFun, Nat.leRecOn_self]
  | succ d ih =>
    simp only [padFun]
    rw [Nat.leRecOn_succ (n := i) (m := i + d) (h1 := Nat.le_add_right i d) (h2 := h)]
    change bdgKreinPair (padSum (padFun i (i + d) (Nat.le_add_right i d) x))
      (padSum (padFun i (i + d) (Nat.le_add_right i d) y)) = bdgKreinPair x y
    rw [padSum_bdgKreinPair]
    exact ih (Nat.le_add_right i d)

/-- The stage bilinear forms are compatible with the directed padding maps. -/
theorem bdgStageKreinBilin_compat (i j : ℕ) (h : i ≤ j) (x y : BdgTowerState i) :
    bdgStageKreinBilin j (padMapLin i j h x) (padMapLin i j h y) =
      bdgStageKreinBilin i x y := by
  simp [bdgStageKreinBilin_apply, padMapLin, padFun_bdgKreinPair]

/-- Native algebraic direct limit of the concrete gapped BdG tower. -/
abbrev BdgTowerDirectLimit : Type :=
  _root_.DirectLimit BdgTowerState (fun i j h => padMapLin i j h)

/-- Indefinite Krein form on the native direct limit of the BdG tower. -/
abbrev bdgLimitKreinForm : LinearMap.BilinForm ℝ BdgTowerDirectLimit :=
  form (fun i j h => padMapLin i j h) bdgStageKreinBilin bdgStageKreinBilin_compat

/-- Same-stage evaluation recovers exactly the finite sheet-Krein pairing. -/
theorem bdgLimitKreinForm_of (i : ℕ) (x y : BdgTowerState i) :
    bdgLimitKreinForm
        (DirectLimit.Module.of ℝ ℕ BdgTowerState (fun i j h => padMapLin i j h) i x)
        (DirectLimit.Module.of ℝ ℕ BdgTowerState (fun i j h => padMapLin i j h) i y) =
      bdgKreinPair x y := by
  simpa [bdgLimitKreinForm, bdgStageKreinBilin_apply] using
    (form_of (fun i j h => padMapLin i j h) bdgStageKreinBilin
      bdgStageKreinBilin_compat i x y)

/-- A purely hole-like stage-one vector has strictly negative sheet-Krein norm. -/
def bdgNegativeStageOne : BdgTowerState 1 := fun i =>
  match i with
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- The explicit stage-one witness has sheet-Krein square `-1`. -/
theorem bdgNegativeStageOne_pair_self :
    bdgKreinPair bdgNegativeStageOne bdgNegativeStageOne = -1 := by
  norm_num [bdgKreinPair, sheetKrein, Matrix.mulVec, dotProduct, bdgNegativeStageOne]

/-- The limit pairing is genuinely indefinite: a nonzero limit vector has
negative sheet-Krein square. -/
theorem bdgLimitKreinForm_indefinite :
    ∃ x : BdgTowerDirectLimit, x ≠ 0 ∧ bdgLimitKreinForm x x < 0 := by
  refine ⟨DirectLimit.Module.of ℝ ℕ BdgTowerState (fun i j h => padMapLin i j h)
    1 bdgNegativeStageOne, ?_⟩
  simpa [bdgLimitKreinForm, bdgStageKreinBilin_apply] using
    (negative_survives (fun i j h => padMapLin i j h) bdgStageKreinBilin
      bdgStageKreinBilin_compat 1 bdgNegativeStageOne
      (by simpa [bdgStageKreinBilin_apply, bdgNegativeStageOne_pair_self]))

end InfoGeometry.Canonical.DoubledMinkowskiBdgDirectLimit
