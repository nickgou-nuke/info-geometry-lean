/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Algebra.PeirceLieJordanResolution
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Lie--Jordan and Peirce transport into the existing matrix-tower colimit

The target is the repository's full noncommutative `Cl11TensorTowerLimit.Limit`,
not the diagonal cylinder model. This file proves intertwining and survival of
an evaluated obstruction. It does not construct an analytic completion or
identify a projective point at infinity with the algebraic colimit.
-/

namespace InfoGeometry.Canonical.LieJordanPeirceColimit

open InfoGeometry.OperatorAlgebra.LieJordanDualTransport
open InfoGeometry.Algebra.PeirceLieJordanResolution
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- Generic corner naturality, specialized below to the actual tower maps. -/
theorem map_cornerOp {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] (f : A →+* B) (p x : A) (i j : Bool) :
    f (cornerOp (R := R) p i j x) = cornerOp (R := R) (f p) i j (f x) := by
  cases i <;> cases j <;>
    simp [cornerOp, endpoint, compIdempotent, map_mul, map_sub]

theorem ofStage_plus (n : ℕ) (h s x : Stage n) :
    ofStage n (plus (R := ℝ) h s x) =
      plus (R := ℝ) (ofStage n h) (ofStage n s) (ofStage n x) :=
  map_plus (R := ℝ) (ofStage n) h s x

theorem ofStage_minus (n : ℕ) (h s x : Stage n) :
    ofStage n (minus (R := ℝ) h s x) =
      minus (R := ℝ) (ofStage n h) (ofStage n s) (ofStage n x) :=
  map_minus (R := ℝ) (ofStage n) h s x

theorem ofStage_cornerOp (n : ℕ) (p x : Stage n) (i j : Bool) :
    ofStage n (cornerOp (R := ℝ) p i j x) =
      cornerOp (R := ℝ) (ofStage n p) i j (ofStage n x) :=
  map_cornerOp (R := ℝ) (ofStage n) p x i j

/-- Transport of the coefficients and observable commutes with refinement. -/
theorem plus_bonding_compatible (n : ℕ) (h s x : Stage n) :
    ofStage (n + 1) (plus (R := ℝ) (stageEmbed n h) (stageEmbed n s) (stageEmbed n x)) =
      ofStage n (plus (R := ℝ) h s x) := by
  calc
    _ = ofStage (n + 1) (stageEmbed n (plus (R := ℝ) h s x)) := by
      exact congrArg (ofStage (n + 1))
        (map_plus (R := ℝ) (stageEmbed n).toRingHom h s x).symm
    _ = _ := ofStage_apply_bond n _

/-- The existing universal map reads the transported operation at its source. -/
theorem lift_plus {B : Type} [Semiring B]
    (f : ∀ n : ℕ, Stage n →+* B) (hf : CompatibleCone stageBond f)
    (n : ℕ) (h s x : Stage n) :
    directLimitLift stageBond f hf
      (plus (R := ℝ) (ofStage n h) (ofStage n s) (ofStage n x)) =
        f n (plus (R := ℝ) h s x) := by
  rw [← ofStage_plus]
  exact directLimitLift_of stageBond f hf n _

/-- No evaluation of the noncommutative composition defect is lost on passage
to the genuine injective matrix-tower colimit. -/
theorem composition_defect_nonzero_iff (n : ℕ) (h s x : Stage n) :
    (minus (R := ℝ) (ofStage n h) (ofStage n s)
        (plus (R := ℝ) (ofStage n h) (ofStage n s) (ofStage n x)) -
      plus (R := ℝ) (ofStage n h) (ofStage n s)
        (minus (R := ℝ) (ofStage n h) (ofStage n s) (ofStage n x)) ≠ 0) ↔
    minus (R := ℝ) h s (plus (R := ℝ) h s x) -
      plus (R := ℝ) h s (minus (R := ℝ) h s x) ≠ 0 := by
  have hinj : Function.Injective (ofStage n) := by
    apply directLimitOf_injective stageBond
    intro k
    change Function.Injective (matStageEmbed k)
    exact matStageEmbed_injective k
  have hm :
      ofStage n (minus (R := ℝ) h s (plus (R := ℝ) h s x) -
        plus (R := ℝ) h s (minus (R := ℝ) h s x)) =
      minus (R := ℝ) (ofStage n h) (ofStage n s)
        (plus (R := ℝ) (ofStage n h) (ofStage n s) (ofStage n x)) -
      plus (R := ℝ) (ofStage n h) (ofStage n s)
        (minus (R := ℝ) (ofStage n h) (ofStage n s) (ofStage n x)) := by
    simp only [map_sub, ofStage_plus, ofStage_minus]
  constructor
  · intro hne hz
    apply hne
    rw [← hm, hz, map_zero]
  · intro hne hz
    apply hne
    apply hinj
    rw [hm, hz, map_zero]

end InfoGeometry.Canonical.LieJordanPeirceColimit
