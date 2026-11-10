/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.ColimitContinuum.TensorTowerColimit
import InfoGeometry.Spectral.Colimit.SequentialModule
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Cartan action on the categorical module colimit of the matrix tower

The finite odd-dimensional matrix stages and their zero-corner embeddings are
already owned by `TensorTowerColimit`.  This file packages those stages as a
sequence in `ModuleCat R` and descends the compatible Cartan commutator maps to
the actual Mathlib colimit.  The result is a module endomorphism; no algebra
colimit structure is asserted for the non-unital embeddings.
-/

noncomputable section

namespace InfoGeometry.ColimitContinuum.CartanActionOnMatrixTowerColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.ColimitContinuum.TensorTowerColimit
open InfoGeometry.Spectral.Colimit.SequentialModule

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem cartanColimit_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

variable {R : Type} [Ring R]

/-- Every entry of `H_tower m` is central (`{-1, 0, 1}`), so left multiplication by
`H_tower m i j` commutes with left scalar multiplication by any `c : R` over any `[Ring R]`. -/
theorem H_tower_entry_mul_comm :
    ∀ (m : ℕ) (i j : Fin (2 * m + 1)) (c r : R),
      H_tower (R := R) m i j * (c * r) = c * (H_tower (R := R) m i j * r)
  | 0, i, j, c, r => by
      simp [H_tower]
  | 1, i, j, c, r => by
      fin_cases i <;> fin_cases j <;> simp [H_tower, H_3, E3]
  | m + 2, i, j, c, r => by
      change embed_sum (k := Fin 2) (H_tower (R := R) (m + 1))
          ((towerEquiv (m + 1)).symm i) ((towerEquiv (m + 1)).symm j) * (c * r) =
        c * (embed_sum (k := Fin 2) (H_tower (R := R) (m + 1))
          ((towerEquiv (m + 1)).symm i) ((towerEquiv (m + 1)).symm j) * r)
      generalize (towerEquiv (m + 1)).symm i = u
      generalize (towerEquiv (m + 1)).symm j = v
      cases u <;> cases v
      · simpa [embed_sum] using H_tower_entry_mul_comm (m + 1) _ _ c r
      · simp [embed_sum]
      · simp [embed_sum]
      · simp [embed_sum]

/-- Left multiplication by `H_tower m` commutes with scalar multiplication `c • X` over any `[Ring R]`. -/
theorem H_tower_mul_smul (m : ℕ) (c : R)
    (X : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) R) :
    H_tower (R := R) m * (c • X) = c • (H_tower (R := R) m * X) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => H_tower_entry_mul_comm m i k c (X k j)

/-- The `n`th stage starts with the existing `M₃(R)` owner stage. -/
abbrev Stage (n : ℕ) := Matrix (Fin (2 * (n + 1) + 1)) (Fin (2 * (n + 1) + 1)) R

/-- The bundled module object corresponding to one matrix stage. -/
abbrev StageObj (n : ℕ) : ModuleCat R := ModuleCat.of R (Stage (R := R) n)

/-- Successor embedding, viewed as an `R`-linear map. -/
def stageBond (n : ℕ) : Stage (R := R) n →ₗ[R] Stage (R := R) (n + 1) where
  toFun := embed_tower (n := n + 1)
  map_add' := embed_tower_add
  map_smul' := embed_tower_smul

/-- The concrete matrix stages as a sequence in `ModuleCat R`. -/
def stageDiagram : ℕ ⥤ ModuleCat R :=
  Functor.ofSequence (X := fun n => StageObj (R := R) n) (fun n =>
    (ModuleCat.ofHom (stageBond (R := R) n) : StageObj (R := R) n ⟶ StageObj (R := R) (n + 1)))

@[simp]
theorem stageDiagram_obj (n : ℕ) :
    (stageDiagram (R := R)).obj n = StageObj (R := R) n := rfl

section ColimitAction

/-- The actual categorical module colimit of the concrete matrix tower over any `[Ring R]`. -/
abbrev TowerColimit : ModuleCat R :=
  InfoGeometry.Spectral.Colimit.SequentialModule.Carrier R (stageDiagram (R := R))

/-- The canonical map from a finite matrix stage into the categorical colimit. -/
abbrev stageInclusion (n : ℕ) :
    (stageDiagram (R := R)).obj n ⟶ TowerColimit (R := R) :=
  InfoGeometry.Spectral.Colimit.SequentialModule.inclusion R n

/-- The tower embeddings are exactly the successor arrows of the diagram. -/
theorem stageDiagram_map_succ {R : Type} [Ring R] (n : ℕ) :
    (stageDiagram (R := R)).map (homOfLE (Nat.le_succ n)) =
      ModuleCat.ofHom (stageBond (R := R) n) := by
  simpa [stageDiagram] using
    (Functor.ofSequence_map_homOfLE_succ
      (f := fun n => ModuleCat.ofHom (stageBond (R := R) n)) n)

/-- The Cartan commutator at stage `n`, as an `R`-linear endomorphism over any `[Ring R]`. -/
def cartanStageEndomorphism (n : ℕ) : Stage (R := R) n →ₗ[R] Stage (R := R) n where
  toFun := ad_H (n + 1)
  map_add' X Y := by
    dsimp [ad_H, ad, TensorTowerColimit.commutator]
    rw [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c X := by
    dsimp [ad_H, ad, TensorTowerColimit.commutator]
    rw [H_tower_mul_smul (n + 1) c X, Matrix.smul_mul, smul_sub]

/-- Its pointwise action is the existing finite-stage `ad_H` operator. -/
@[simp]
theorem cartanStageEndomorphism_apply (n : ℕ) (X : Stage (R := R) n) :
    cartanStageEndomorphism (R := R) n X = ad_H (n + 1) X := by
  rfl

/-- The Cartan operators commute with every successor bond. -/
theorem stageBond_cartan_naturality (n : ℕ) :
    cartanStageEndomorphism (R := R) (n + 1) ∘ₗ stageBond (R := R) n =
      stageBond (R := R) n ∘ₗ cartanStageEndomorphism (R := R) n := by
  apply LinearMap.ext
  intro X
  change InfoGeometry.ColimitContinuum.TensorTowerColimit.ad_H
      (n + 2) (embed_tower X) =
    embed_tower (InfoGeometry.ColimitContinuum.TensorTowerColimit.ad_H (n + 1) X)
  exact (embed_tower_ad_H n X).symm

/-- The compatible stagewise Cartan endomorphisms, packaged as a natural
endomorphism of the sequence.  Mathlib's `NatTrans.ofSequence` reduces the
compatibility proof to the successor bonds. -/
def cartanStageFamily : stageDiagram (R := R) ⟶ stageDiagram (R := R) :=
  NatTrans.ofSequence
    (fun n =>
      (ModuleCat.ofHom (cartanStageEndomorphism (R := R) n) :
        StageObj (R := R) n ⟶ StageObj (R := R) n))
    (by
      intro n
      rw [stageDiagram_map_succ]
      simpa [stageDiagram_obj, ModuleCat.hom_comp] using
        congrArg ModuleCat.ofHom (stageBond_cartan_naturality (R := R) n))

/-- The cocone obtained by postcomposing the canonical stage maps with the
compatible finite-stage Cartan operators. -/
def cartanEndomorphismCocone : Cocone R (stageDiagram (R := R)) where
  pt := TowerColimit (R := R)
  ι := cartanStageFamily (R := R) ≫ (colimit.cocone (stageDiagram (R := R))).ι

/-- The induced Cartan endomorphism on the actual categorical module colimit. -/
def cartanColimitEndomorphism : TowerColimit (R := R) ⟶ TowerColimit (R := R) :=
  InfoGeometry.Spectral.Colimit.SequentialModule.descend R
    (cartanEndomorphismCocone (R := R))

/-- Stage readback for the induced Cartan endomorphism. -/
@[simp]
theorem cartanColimitEndomorphism_stage (n : ℕ) :
    stageInclusion (R := R) n ≫ cartanColimitEndomorphism (R := R) =
      cartanStageFamily (R := R).app n ≫ stageInclusion (R := R) n := by
  exact InfoGeometry.Spectral.Colimit.SequentialModule.descend_fac R
    (cartanEndomorphismCocone (R := R)) n

/-- Pointwise stage readback: the induced operator acts on a represented matrix
by its existing finite-stage Cartan commutator. -/
theorem cartanColimitEndomorphism_apply_stage (n : ℕ) (X : Stage (R := R) n) :
    (cartanColimitEndomorphism (R := R)).hom
        ((stageInclusion (R := R) n).hom X) =
      (stageInclusion (R := R) n).hom (ad_H (n + 1) X) := by
  have h := congrArg ModuleCat.Hom.hom
    (cartanColimitEndomorphism_stage (R := R) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
  have hX := congrArg (fun f => f X) h
  change (cartanColimitEndomorphism (R := R)).hom
      ((stageInclusion (R := R) n).hom X) =
    (stageInclusion (R := R) n).hom
      ((cartanStageEndomorphism (R := R) n) X) at hX
  simpa [cartanStageEndomorphism_apply] using hX

/-- The colimit action is uniquely determined by its finite-stage readbacks. -/
theorem cartanColimitEndomorphism_unique
    (f : TowerColimit (R := R) ⟶ TowerColimit (R := R))
    (hf : ∀ n : ℕ,
      stageInclusion (R := R) n ≫ f =
        cartanStageFamily (R := R).app n ≫ stageInclusion (R := R) n) :
    f = cartanColimitEndomorphism (R := R) := by
  apply colimit.hom_ext
  intro n
  exact (hf n).trans (cartanColimitEndomorphism_stage (R := R) n).symm

end ColimitAction

end InfoGeometry.ColimitContinuum.CartanActionOnMatrixTowerColimit

end
