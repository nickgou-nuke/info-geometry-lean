/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Colimit.Module
import InfoGeometry.Canonical.SplitCliffordDirectLimit

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordDirectLimitShift

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge

private abbrev Stage := SplitClNNAlg
private def stageMap (m n : ℕ) (h : m ≤ n) : Stage m →ₗ[ℝ] Stage n :=
  (splitCliffordMap m n h).toLinearMap
private def tailMap (k m n : ℕ) (h : m ≤ n) :
    Stage (m + k) →ₗ[ℝ] Stage (n + k) :=
  stageMap (m + k) (n + k) (Nat.add_le_add_right h k)

abbrev SplitCliffordModuleLimit :=
  Module.DirectLimit Stage (fun m n h => stageMap m n h)
abbrev SplitCliffordTailModuleLimit (k : ℕ) :=
  Module.DirectLimit (fun n => Stage (n + k)) (fun m n h => tailMap k m n h)

private def intoTail (k n : ℕ) : Stage n →ₗ[ℝ] Stage (n + k) :=
  stageMap n (n + k) (Nat.le_add_right n k)

private theorem intoTail_natural (k m n : ℕ) (h : m ≤ n) :
    (intoTail k n).comp (stageMap m n h) =
      (tailMap k m n h).comp (intoTail k m) := by
  ext x
  change splitCliffordMap n (n + k) (Nat.le_add_right n k)
      (splitCliffordMap m n h x) =
    splitCliffordMap (m + k) (n + k) (Nat.add_le_add_right h k)
      (splitCliffordMap m (m + k) (Nat.le_add_right m k) x)
  calc
    _ = splitCliffordMap m (n + k)
        (Nat.le_trans h (Nat.le_add_right n k)) x :=
      (splitCliffordMap_apply_trans m n (n + k) h
        (Nat.le_add_right n k) x).symm
    _ = _ :=
      splitCliffordMap_apply_trans m (m + k) (n + k)
        (Nat.le_add_right m k) (Nat.add_le_add_right h k) x

private theorem toTail_natural (k m n : ℕ) (h : m ≤ n) (x : Stage m) :
    Module.DirectLimit.of ℝ ℕ (fun i => Stage (i + k))
        (fun i j h => tailMap k i j h) n (intoTail k n (stageMap m n h x)) =
      Module.DirectLimit.of ℝ ℕ (fun i => Stage (i + k))
        (fun i j h => tailMap k i j h) m (intoTail k m x) := by
  have hPoint := congrArg
    (fun y => Module.DirectLimit.of ℝ ℕ (fun i => Stage (i + k))
      (fun i j h => tailMap k i j h) n y)
    (LinearMap.congr_fun (intoTail_natural k m n h) x)
  exact hPoint.trans (Module.DirectLimit.of_f (R := ℝ) (ι := ℕ)
    (G := fun i => Stage (i + k)) (f := fun i j h => tailMap k i j h)
    (hij := h) (x := intoTail k m x))

private theorem fromTail_natural (k m n : ℕ) (h : m ≤ n) (x : Stage (m + k)) :
    Module.DirectLimit.of ℝ ℕ Stage (fun i j h => stageMap i j h)
        (n + k) (tailMap k m n h x) =
      Module.DirectLimit.of ℝ ℕ Stage (fun i j h => stageMap i j h)
        (m + k) x := by
  exact Module.DirectLimit.of_f (R := ℝ) (ι := ℕ)
    (G := Stage) (f := fun i j h => stageMap i j h)
    (hij := Nat.add_le_add_right h k) (x := x)

private noncomputable def toTail (k : ℕ) :
    SplitCliffordModuleLimit →ₗ[ℝ] SplitCliffordTailModuleLimit k :=
  Module.DirectLimit.lift ℝ ℕ Stage
    (fun m n h => stageMap m n h)
    (fun n => (Module.DirectLimit.of ℝ ℕ (fun i => Stage (i + k))
      (fun i j h => tailMap k i j h) n).comp (intoTail k n))
    (by
      intro m n h x
      exact toTail_natural k m n h x)

private noncomputable def fromTail (k : ℕ) :
    SplitCliffordTailModuleLimit k →ₗ[ℝ] SplitCliffordModuleLimit :=
  Module.DirectLimit.lift ℝ ℕ (fun n => Stage (n + k))
    (fun m n h => tailMap k m n h)
    (fun n => Module.DirectLimit.of ℝ ℕ Stage
      (fun i j h => stageMap i j h) (n + k))
    (by
      intro m n h x
      exact fromTail_natural k m n h x)

/-- The split Clifford direct limit is linearly equivalent to every fixed
cofinal tail, via the tower's actual transition maps. -/
noncomputable def splitCliffordModuleLimit_shift_equiv (k : ℕ) :
    SplitCliffordModuleLimit ≃ₗ[ℝ] SplitCliffordTailModuleLimit k := by
  refine LinearEquiv.ofLinearMap (toTail k) (fromTail k) ?_ ?_
  · apply Module.DirectLimit.hom_ext
    intro n
    ext x
    change toTail k (fromTail k
      (Module.DirectLimit.of ℝ ℕ (fun i => Stage (i + k))
        (fun i j h => tailMap k i j h) n x)) =
      Module.DirectLimit.of ℝ ℕ (fun i => Stage (i + k))
        (fun i j h => tailMap k i j h) n x
    rw [fromTail, Module.DirectLimit.lift_of, toTail,
      Module.DirectLimit.lift_of, LinearMap.comp_apply]
    exact Module.DirectLimit.of_f (R := ℝ) (ι := ℕ)
      (G := fun i => Stage (i + k)) (f := fun i j h => tailMap k i j h)
      (hij := Nat.le_add_right n k) (x := x)
  · apply Module.DirectLimit.hom_ext
    intro n
    ext x
    change fromTail k (toTail k
      (Module.DirectLimit.of ℝ ℕ Stage
        (fun i j h => stageMap i j h) n x)) =
      Module.DirectLimit.of ℝ ℕ Stage
        (fun i j h => stageMap i j h) n x
    rw [toTail, Module.DirectLimit.lift_of, LinearMap.comp_apply,
      fromTail, Module.DirectLimit.lift_of]
    exact Module.DirectLimit.of_f (R := ℝ) (ι := ℕ)
      (G := Stage) (f := fun i j h => stageMap i j h)
      (hij := Nat.le_add_right n k) (x := x)

end InfoGeometry.Canonical.SplitCliffordDirectLimitShift

end
