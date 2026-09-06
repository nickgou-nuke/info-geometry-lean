import InfoGeometry.Canonical.CuntzMatrixTraceTower
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Algebraic star colimit of the raw Cuntz matrix tower

The matrix stages are used only with their native ring, complex-algebra, and
star structures.  No norm or `CStarAlgebra` instance is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit

open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

def rawMap {i j : ℕ} (hij : i ≤ j) :
    MatrixStage i →⋆ₐ[ℂ] MatrixStage j :=
  concreteMap hij

instance rawDirectedSystem :
    DirectedSystem MatrixStage
      (fun _ _ hij => rawMap hij) where
  map_self := by
    intro i x
    exact congrArg (fun f => f x) (concreteMap_id i)
  map_map := by
    intro i j k hij hjk x
    simpa [rawMap] using
      congrArg (fun f => f x) (concreteMap_comp hij hjk)

abbrev Carrier : Type :=
  DirectLimit MatrixStage (fun _ _ hij => rawMap hij)

instance carrierAlgebra : Algebra ℂ Carrier :=
  Algebra.ofModule
    (by
      intro c x y
      induction x, y using DirectLimit.induction₂ with
      | _ i x y => simp [DirectLimit.smul_def, DirectLimit.mul_def])
    (by
      intro c x y
      induction x, y using DirectLimit.induction₂ with
      | _ i x y => simp [DirectLimit.smul_def, DirectLimit.mul_def])

instance carrierStar : Star Carrier where
  star :=
    DirectLimit.map
      (fun _ _ hij => rawMap hij)
      (fun _ _ hij => rawMap hij)
      (fun _ x => star x)
      (by
        intro i j hij x
        exact map_star (rawMap hij) x)

@[simp] theorem star_mk (i : ℕ) (x : MatrixStage i) :
    star (⟦⟨i, x⟩⟧ : Carrier) =
      (⟦⟨i, star x⟩⟧ : Carrier) := rfl

instance carrierStarRing : StarRing Carrier where
  star_involutive := by
    intro x
    induction x using DirectLimit.induction with
    | _ i x => simp [star_mk]
  star_add := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ i x y =>
        rw [DirectLimit.add_def, star_mk, star_mk, star_mk,
          DirectLimit.add_def, star_add]
  star_mul := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ i x y =>
        rw [DirectLimit.mul_def, star_mk, star_mk, star_mk,
          DirectLimit.mul_def, star_mul]

def stageInjection (i : ℕ) : MatrixStage i →⋆ₐ[ℂ] Carrier where
  toFun := DirectLimit.Ring.of MatrixStage
    (fun _ _ hij => rawMap hij) i
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change (⟦⟨i, c • 1⟩⟧ : Carrier) = c • (1 : Carrier)
    rw [DirectLimit.one_def i, DirectLimit.smul_def]
  map_star' := by
    intro x
    rfl

@[simp] theorem stageInjection_apply (i : ℕ) (x : MatrixStage i) :
    stageInjection i x = (⟦⟨i, x⟩⟧ : Carrier) := rfl

@[simp] theorem stageInjection_add (i : ℕ) (x y : MatrixStage i) :
    stageInjection i (x + y) = stageInjection i x + stageInjection i y := by
  exact map_add (stageInjection i) x y

@[simp] theorem stageInjection_mul (i : ℕ) (x y : MatrixStage i) :
    stageInjection i (x * y) = stageInjection i x * stageInjection i y := by
  exact map_mul (stageInjection i) x y

@[simp] theorem stageInjection_star (i : ℕ) (x : MatrixStage i) :
    stageInjection i (star x) = star (stageInjection i x) := by
  exact map_star (stageInjection i) x

@[simp] theorem stageInjection_smul (i : ℕ) (c : ℂ) (x : MatrixStage i) :
    stageInjection i (c • x) = c • stageInjection i x := by
  exact map_smul (stageInjection i) c x

theorem stageInjection_transition {i j : ℕ} (hij : i ≤ j) (x : MatrixStage i) :
    stageInjection j (rawMap hij x) = stageInjection i x := by
  exact DirectLimit.Ring.of_f
    (G := MatrixStage) (f := fun _ _ hij => rawMap hij) hij x

theorem stageInjection_concrete_transition {i j : ℕ} (hij : i ≤ j)
    (x : MatrixStage i) :
    stageInjection j (concreteMap hij x) = stageInjection i x := by
  exact stageInjection_transition hij x

end InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
