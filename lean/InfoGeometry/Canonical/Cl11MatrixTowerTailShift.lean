/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11TensorTowerLimit

noncomputable section

namespace InfoGeometry.Canonical.Cl11MatrixTowerTailShift

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

private abbrev Stage := InfoGeometry.Clifford.Cl11TensorTower.MatStage
private abbrev BaseLimit := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

private def tailMap (k m n : ℕ) (h : m ≤ n) :
    Stage (m + k) →+* Stage (n + k) :=
  bondMap stageBond (m + k) (n + k) (Nat.add_le_add_right h k)

private instance tailDirectedSystem (k : ℕ) :
    DirectedSystem (fun n : ℕ => Stage (n + k))
      (fun m n h => tailMap k m n h) where
  map_self := by
    intro n x
    change bondMap stageBond (n + k) (n + k) _ x = x
    simp
  map_map := by
    intro n j i hij hjn x
    change bondMap stageBond (j + k) (n + k) _
        (bondMap stageBond (i + k) (j + k) _ x) =
      bondMap stageBond (i + k) (n + k) _ x
    exact (bondMap_apply_trans stageBond (i + k) (j + k) (n + k)
      (Nat.add_le_add_right hij k) (Nat.add_le_add_right hjn k) x).symm

/-- The algebraic direct limit of the matrix tower beginning at stage `k`. -/
abbrev TailLimit (k : ℕ) :=
  _root_.DirectLimit (fun n : ℕ => Stage (n + k))
    (fun m n h => tailMap k m n h)

private def tailOf (k n : ℕ) : Stage (n + k) →+* TailLimit k :=
  DirectLimit.Ring.of (fun n : ℕ => Stage (n + k))
    (fun m n h => tailMap k m n h) n

private def limitOf (n : ℕ) : Stage n →+* BaseLimit :=
  directLimitOf stageBond n

private def intoTail (k n : ℕ) : Stage n →+* Stage (n + k) :=
  bondMap stageBond n (n + k) (Nat.le_add_right n k)

private theorem intoTail_natural (k m n : ℕ) (h : m ≤ n) :
    (intoTail k n).comp (bondMap stageBond m n h) =
      (tailMap k m n h).comp (intoTail k m) := by
  apply RingHom.ext
  intro x
  change bondMap stageBond n (n + k) (Nat.le_add_right n k)
      (bondMap stageBond m n h x) =
    bondMap stageBond (m + k) (n + k) (Nat.add_le_add_right h k)
      (bondMap stageBond m (m + k) (Nat.le_add_right m k) x)
  calc
    _ = bondMap stageBond m (n + k)
        (Nat.le_trans h (Nat.le_add_right n k)) x := by
      exact (bondMap_apply_trans stageBond m n (n + k) h
        (Nat.le_add_right n k) x).symm
    _ = _ := bondMap_apply_trans stageBond m (m + k) (n + k)
      (Nat.le_add_right m k) (Nat.add_le_add_right h k) x

private def toTail (k : ℕ) : BaseLimit →+* TailLimit k :=
  DirectLimit.Ring.lift Stage
    (fun m n h => bondMap stageBond m n h)
    (TailLimit k)
    (fun n => (tailOf k n).comp (intoTail k n))
    (by
      intro m n h x
      change tailOf k n (intoTail k n (bondMap stageBond m n h x)) =
        tailOf k m (intoTail k m x)
      calc
        _ = tailOf k n (tailMap k m n h (intoTail k m x)) := by
          exact congrArg (tailOf k n)
            (RingHom.congr_fun (intoTail_natural k m n h) x)
        _ = _ := DirectLimit.Ring.of_f
          (G := fun n : ℕ => Stage (n + k))
          (f := fun i j h => tailMap k i j h)
          (hij := h) (x := intoTail k m x))

private def fromTail (k : ℕ) : TailLimit k →+* BaseLimit :=
  DirectLimit.Ring.lift (fun n : ℕ => Stage (n + k))
    (fun m n h => tailMap k m n h)
    BaseLimit
    (fun n => limitOf (n + k))
    (by
      intro m n h x
      exact DirectLimit.Ring.of_f
        (G := Stage) (f := fun i j h => bondMap stageBond i j h)
        (Nat.add_le_add_right h k) x)

private theorem toTail_fromTail (k : ℕ) :
    (toTail k).comp (fromTail k) = RingHom.id (TailLimit k) := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext x
  change toTail k (fromTail k (tailOf k n x)) = tailOf k n x
  simp only [fromTail, toTail, DirectLimit.Ring.lift_of,
    tailOf, limitOf, intoTail]
  change tailOf k (n + k) (bondMap stageBond (n + k) ((n + k) + k) _ x) =
    tailOf k n x
  exact DirectLimit.Ring.of_f
    (G := fun n : ℕ => Stage (n + k))
    (f := fun i j h => tailMap k i j h)
    (hij := Nat.le_add_right n k) x

private theorem fromTail_toTail (k : ℕ) :
    (fromTail k).comp (toTail k) = RingHom.id BaseLimit := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext x
  change fromTail k (toTail k (limitOf n x)) = limitOf n x
  simp only [toTail, fromTail,
    tailOf, limitOf, intoTail]
  change limitOf (n + k) (bondMap stageBond n (n + k) _ x) = limitOf n x
  exact DirectLimit.Ring.of_f
    (G := Stage) (f := fun i j h => bondMap stageBond i j h)
    (hij := Nat.le_add_right n k) x

/-- The algebraic matrix `Cl(1,1)` tower limit is ring-isomorphic to each
fixed finite tail, using the actual iterated tower embeddings. -/
def cl11MatrixLimit_tailRingEquiv (k : ℕ) :
    BaseLimit ≃+* TailLimit k :=
  RingEquiv.ofRingHom (toTail k) (fromTail k)
    (toTail_fromTail k) (fromTail_toTail k)

/-- On a finite-stage representative, the shift is the canonical transition
from stage `n` to stage `n + k` in the tail system. -/
@[simp] theorem cl11MatrixLimit_tailRingEquiv_ofStage
    (k n : ℕ) (x : Stage n) :
    cl11MatrixLimit_tailRingEquiv k (ofStage n x) =
      tailOf k n (bondMap stageBond n (n + k) (Nat.le_add_right n k) x) := by
  change toTail k (limitOf n x) = tailOf k n (intoTail k n x)
  simp only [toTail, limitOf, directLimitOf, DirectLimit.Ring.lift_of,
    RingHom.comp_apply, tailOf, intoTail]

end InfoGeometry.Canonical.Cl11MatrixTowerTailShift

end
