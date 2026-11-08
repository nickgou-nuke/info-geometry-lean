/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitCliffordSuperGradeColimit

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordDirectLimitRingShift

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.CliffordTower

private abbrev Stage := SplitClNNAlg

private def tailMap (k m n : ℕ) (h : m ≤ n) :
    Stage (m + k) →ₐ[ℝ] Stage (n + k) :=
  splitCliffordMap (m + k) (n + k) (Nat.add_le_add_right h k)

private instance tailDirectedSystem (k : ℕ) :
    DirectedSystem (fun n : ℕ => Stage (n + k))
      (fun m n h => tailMap k m n h) where
  map_self := by
    intro n x
    change splitCliffordMap (n + k) (n + k) _ x = x
    simp
  map_map := by
    intro n j i hij hjn x
    change splitCliffordMap (j + k) (n + k) _
        (splitCliffordMap (i + k) (j + k) _ x) =
      splitCliffordMap (i + k) (n + k) _ x
    exact (splitCliffordMap_apply_trans (i + k) (j + k) (n + k)
      (Nat.add_le_add_right hij k) (Nat.add_le_add_right hjn k) x).symm

/-- The algebraic direct limit of the split Clifford tower beginning at stage `k`. -/
abbrev SplitCliffordTailInfinity (k : ℕ) :=
  _root_.DirectLimit (fun n : ℕ => Stage (n + k)) (fun m n h => tailMap k m n h)

noncomputable instance splitCliffordTailInfinityModule (k : ℕ) :
    Module ℝ (SplitCliffordTailInfinity k) := DirectLimit.instModule

/-- Canonical map from a finite tail stage into its direct limit. -/
noncomputable def splitCliffordTailOf (k n : ℕ) :
    SplitClNNAlg (n + k) →+* SplitCliffordTailInfinity k :=
  DirectLimit.Ring.of (fun n : ℕ => Stage (n + k))
    (fun m n h => tailMap k m n h) n

/-- Every canonical finite-stage map into a cofinal tail is injective. -/
theorem splitCliffordTailInfinity_stage_injective (k n : ℕ) :
    Function.Injective (splitCliffordTailOf k n) := by
  exact DirectLimit.mk_injective
    (f := fun i j h => tailMap k i j h)
    (fun i j hij => splitCliffordMap_injective
      (Nat.add_le_add_right hij k)) n

private def splitOf (n : ℕ) : Stage n →+* SplitCliffordInfinity :=
  DirectLimit.Ring.of Stage (fun m n h => splitCliffordMap m n h) n

private def intoTail (k n : ℕ) : Stage n →+* Stage (n + k) :=
  (splitCliffordMap n (n + k) (Nat.le_add_right n k)).toRingHom

private theorem intoTail_natural (k m n : ℕ) (h : m ≤ n) :
    (intoTail k n).comp ((splitCliffordMap m n h).toRingHom) =
      (tailMap k m n h).toRingHom.comp (intoTail k m) := by
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

private def toTail (k : ℕ) : SplitCliffordInfinity →+* SplitCliffordTailInfinity k :=
  DirectLimit.Ring.lift Stage
    (fun m n h => splitCliffordMap m n h)
    (SplitCliffordTailInfinity k)
    (fun n => (splitCliffordTailOf k n).comp (intoTail k n))
    (by
      intro m n h x
      change splitCliffordTailOf k n (intoTail k n (splitCliffordMap m n h x)) =
        splitCliffordTailOf k m (intoTail k m x)
      calc
        _ = splitCliffordTailOf k n
            (tailMap k m n h (intoTail k m x)) := by
              exact congrArg (splitCliffordTailOf k n)
                (RingHom.congr_fun (intoTail_natural k m n h) x)
        _ = _ := DirectLimit.Ring.of_f
          (G := fun n : ℕ => Stage (n + k))
          (f := fun i j h => tailMap k i j h)
          (hij := h) (x := intoTail k m x))

private def fromTail (k : ℕ) : SplitCliffordTailInfinity k →+* SplitCliffordInfinity :=
  DirectLimit.Ring.lift (fun n : ℕ => Stage (n + k))
    (fun m n h => tailMap k m n h)
    SplitCliffordInfinity
    (fun n => splitOf (n + k))
    (by
      intro m n h x
      exact DirectLimit.Ring.of_f
        (G := Stage)
        (f := fun i j h => splitCliffordMap i j h)
        (Nat.add_le_add_right h k) x)

private theorem toTail_fromTail (k : ℕ) :
    (toTail k).comp (fromTail k) = RingHom.id (SplitCliffordTailInfinity k) := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext x
  change toTail k (fromTail k (splitCliffordTailOf k n x)) = splitCliffordTailOf k n x
  simp only [fromTail, toTail, DirectLimit.Ring.lift_of, RingHom.comp_apply,
    splitCliffordTailOf, splitOf, intoTail]
  change splitCliffordTailOf k (n + k) (intoTail k (n + k) x) = splitCliffordTailOf k n x
  exact DirectLimit.Ring.of_f
    (G := fun n : ℕ => Stage (n + k))
    (f := fun i j h => tailMap k i j h)
    (hij := Nat.le_add_right n k) x

private theorem fromTail_toTail (k : ℕ) :
    (fromTail k).comp (toTail k) = RingHom.id SplitCliffordInfinity := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext x
  change fromTail k (toTail k (splitOf n x)) = splitOf n x
  simp only [toTail, fromTail, DirectLimit.Ring.lift_of, RingHom.comp_apply,
    splitCliffordTailOf, splitOf, intoTail]
  change splitOf (n + k) (intoTail k n x) = splitOf n x
  exact DirectLimit.Ring.of_f
    (G := Stage)
    (f := fun i j h => splitCliffordMap i j h)
    (hij := Nat.le_add_right n k) x

/-- The split Clifford algebraic direct limit is ring-isomorphic to each
cofinal tail, using the tower's actual algebra homomorphisms. -/
def splitCliffordInfinity_ring_shift_equiv (k : ℕ) :
    SplitCliffordInfinity ≃+* SplitCliffordTailInfinity k :=
  RingEquiv.ofRingHom (toTail k) (fromTail k)
    (toTail_fromTail k) (fromTail_toTail k)

/-- On a canonical finite-stage image, the ring shift is exactly the tower's
transition to the stage `n + k` in the tail system. -/
@[simp] theorem splitCliffordInfinity_ring_shift_equiv_ofStage
    (k n : ℕ) (x : Stage n) :
    splitCliffordInfinity_ring_shift_equiv k
        (DirectLimit.Ring.of Stage (fun i j h => splitCliffordMap i j h) n x) =
      DirectLimit.Ring.of (fun i : ℕ => Stage (i + k))
        (fun i j h => tailMap k i j h) n
        (splitCliffordMap n (n + k) (Nat.le_add_right n k) x) := by
  change toTail k (splitOf n x) = splitCliffordTailOf k n (intoTail k n x)
  simp only [toTail, splitOf, DirectLimit.Ring.lift_of, RingHom.comp_apply,
    splitCliffordTailOf, intoTail]

/-- The inverse shift sends a tail-stage image back to the same element at
the corresponding original stage. -/
@[simp] theorem splitCliffordInfinity_ring_shift_equiv_symm_ofTail
    (k n : ℕ) (x : Stage (n + k)) :
    (splitCliffordInfinity_ring_shift_equiv k).symm
        (DirectLimit.Ring.of (fun i : ℕ => Stage (i + k))
          (fun i j h => tailMap k i j h) n x) =
      DirectLimit.Ring.of Stage (fun i j h => splitCliffordMap i j h)
        (n + k) x := by
  change fromTail k (splitCliffordTailOf k n x) = splitOf (n + k) x
  simp only [fromTail, splitCliffordTailOf, splitOf, DirectLimit.Ring.lift_of]

/-- The cofinal-tail ring equivalence preserves the canonical real scalar
maps, so it is an equivalence of real algebras. -/
theorem splitCliffordInfinity_ring_shift_equiv_commutes (k : ℕ) (r : ℝ) :
    splitCliffordInfinity_ring_shift_equiv k
        (algebraMap ℝ SplitCliffordInfinity r) =
      algebraMap ℝ (SplitCliffordTailInfinity k) r := by
  rw [DirectLimit.algebraMap_def (G := Stage)
        (f := fun i j h => splitCliffordMap i j h) 0 r,
      DirectLimit.algebraMap_def (G := fun n : ℕ => Stage (n + k))
        (f := fun i j h => tailMap k i j h) 0 r]
  change splitCliffordInfinity_ring_shift_equiv k
      (DirectLimit.Ring.of Stage (fun i j h => splitCliffordMap i j h) 0
        (algebraMap ℝ (Stage 0) r)) =
    DirectLimit.Ring.of (fun n : ℕ => Stage (n + k))
      (fun m n h => tailMap k m n h) 0
      (algebraMap ℝ (Stage (0 + k)) r)
  rw [splitCliffordInfinity_ring_shift_equiv_ofStage]
  congr 1
  exact (splitCliffordMap 0 (0 + k) (Nat.le_add_right 0 k)).commutes r

/-- The canonical cofinal-tail identification is an `ℝ`-algebra equivalence. -/
noncomputable def splitCliffordInfinity_alg_shift_equiv (k : ℕ) :
    SplitCliffordInfinity ≃ₐ[ℝ] SplitCliffordTailInfinity k :=
  AlgEquiv.ofRingEquiv (f := splitCliffordInfinity_ring_shift_equiv k)
    (splitCliffordInfinity_ring_shift_equiv_commutes k)

/-- The grade involution induced on the algebraic direct limit of the tail
beginning at stage `k`. -/
noncomputable def splitCliffordTailInfinityInvolute (k : ℕ) :
    SplitCliffordTailInfinity k →+* SplitCliffordTailInfinity k :=
  DirectLimit.Ring.lift (fun n : ℕ => Stage (n + k))
    (fun m n h => tailMap k m n h)
    (SplitCliffordTailInfinity k)
    (fun n => (splitCliffordTailOf k n).comp
      (CliffordAlgebra.involute (Q := Qsplit (n + k))).toRingHom)
    (by
      intro m n h x
      change splitCliffordTailOf k n
          (CliffordAlgebra.involute (Q := Qsplit (n + k))
            (tailMap k m n h x)) =
        splitCliffordTailOf k m (CliffordAlgebra.involute (Q := Qsplit (m + k)) x)
      calc
        _ = splitCliffordTailOf k n
            (tailMap k m n h
              (CliffordAlgebra.involute (Q := Qsplit (m + k)) x)) := by
                exact congrArg (splitCliffordTailOf k n)
                  (splitCliffordMap_involute (m + k) (n + k)
                    (Nat.add_le_add_right h k) x)
        _ = _ := DirectLimit.Ring.of_f
          (G := fun n : ℕ => Stage (n + k))
          (f := fun i j h => tailMap k i j h)
          (hij := h) (CliffordAlgebra.involute (Q := Qsplit (m + k)) x))

/-- The tail grade involution acts stagewise by Mathlib's Clifford grade
involution. -/
@[simp] theorem splitCliffordTailInfinityInvolute_ofStage
    (k n : ℕ) (x : SplitClNNAlg (n + k)) :
    splitCliffordTailInfinityInvolute k (splitCliffordTailOf k n x) =
      splitCliffordTailOf k n (CliffordAlgebra.involute (Q := Qsplit (n + k)) x) := by
  change DirectLimit.Ring.lift (fun n : ℕ => Stage (n + k))
      (fun m n h => tailMap k m n h)
      (SplitCliffordTailInfinity k)
      (fun n => (splitCliffordTailOf k n).comp
        (CliffordAlgebra.involute (Q := Qsplit (n + k))).toRingHom) _
      (DirectLimit.Ring.of (fun n : ℕ => Stage (n + k))
        (fun m n h => tailMap k m n h) n x) = _
  rw [DirectLimit.Ring.lift_of]
  rfl

/-- The cofinal-tail grade involution is compatible with the direct-limit
real module structure, since each finite Clifford grade involution is an
`ℝ`-algebra homomorphism. -/
theorem splitCliffordTailInfinityInvolute_smul (k : ℕ) (r : ℝ)
    (x : SplitCliffordTailInfinity k) :
    splitCliffordTailInfinityInvolute k (r • x) =
      r • splitCliffordTailInfinityInvolute k x := by
  induction x using DirectLimit.induction with
  | _ n a =>
      change splitCliffordTailInfinityInvolute k
          (splitCliffordTailOf k n (r • a)) =
        r • splitCliffordTailInfinityInvolute k
          (splitCliffordTailOf k n a)
      rw [splitCliffordTailInfinityInvolute_ofStage,
        splitCliffordTailInfinityInvolute_ofStage]
      change DirectLimit.Module.of ℝ ℕ (fun i : ℕ => Stage (i + k))
          (fun i j h => tailMap k i j h) n
          (CliffordAlgebra.involute (Q := Qsplit (n + k)) (r • a)) =
        r • DirectLimit.Module.of ℝ ℕ (fun i : ℕ => Stage (i + k))
          (fun i j h => tailMap k i j h) n
          (CliffordAlgebra.involute (Q := Qsplit (n + k)) a)
      rw [map_smul, map_smul]

/-- The induced grade involution on every cofinal tail is involutive. -/
theorem splitCliffordTailInfinityInvolute_involutive (k : ℕ)
    (x : SplitCliffordTailInfinity k) :
    splitCliffordTailInfinityInvolute k
        (splitCliffordTailInfinityInvolute k x) = x := by
  induction x using DirectLimit.induction with
  | _ n a =>
      calc
        splitCliffordTailInfinityInvolute k
            (splitCliffordTailInfinityInvolute k (splitCliffordTailOf k n a)) =
          splitCliffordTailOf k n
            (CliffordAlgebra.involute (Q := Qsplit (n + k))
              (CliffordAlgebra.involute (Q := Qsplit (n + k)) a)) := rfl
        _ = splitCliffordTailOf k n a := by
          rw [CliffordAlgebra.involute_involute]

/-- A finite even Clifford element gives a fixed element in every tail
direct limit. -/
theorem splitCliffordTailInfinity_of_even_fixed
    (k n : ℕ) {x : SplitClNNAlg (n + k)}
    (hx : x ∈ CliffordAlgebra.evenOdd (Qsplit (n + k)) 0) :
    splitCliffordTailInfinityInvolute k (splitCliffordTailOf k n x) =
      splitCliffordTailOf k n x := by
  change splitCliffordTailOf k n
      (CliffordAlgebra.involute (Q := Qsplit (n + k)) x) = _
  rw [CliffordAlgebra.involute_eq_of_mem_even hx]

/-- A finite odd Clifford element gives a negative eigenvector in every tail
direct limit. -/
theorem splitCliffordTailInfinity_of_odd_negated
    (k n : ℕ) {x : SplitClNNAlg (n + k)}
    (hx : x ∈ CliffordAlgebra.evenOdd (Qsplit (n + k)) 1) :
    splitCliffordTailInfinityInvolute k (splitCliffordTailOf k n x) =
      -splitCliffordTailOf k n x := by
  change splitCliffordTailOf k n
      (CliffordAlgebra.involute (Q := Qsplit (n + k)) x) = _
  rw [CliffordAlgebra.involute_eq_of_mem_odd hx, map_neg]

/-- The cofinal-tail ring equivalence intertwines the lifted Clifford grade
involutions on the original and shifted algebraic direct limits. -/
theorem splitCliffordInfinity_ring_shift_equiv_grade_involution (k : ℕ) :
    (splitCliffordTailInfinityInvolute k).comp
        (splitCliffordInfinity_ring_shift_equiv k).toRingHom =
      (splitCliffordInfinity_ring_shift_equiv k).toRingHom.comp
        splitCliffordInfinityInvolute.toRingHom := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext x
  change splitCliffordTailInfinityInvolute k
      (splitCliffordInfinity_ring_shift_equiv k (splitOf n x)) =
    splitCliffordInfinity_ring_shift_equiv k
      (splitOf n (CliffordAlgebra.involute (Q := Qsplit n) x))
  change splitCliffordTailOf k n
      (CliffordAlgebra.involute (Q := Qsplit (n + k))
        (splitCliffordMap n (n + k) (Nat.le_add_right n k) x)) =
    splitCliffordTailOf k n
      (splitCliffordMap n (n + k) (Nat.le_add_right n k)
        (CliffordAlgebra.involute (Q := Qsplit n) x))
  exact congrArg (splitCliffordTailOf k n)
    (splitCliffordMap_involute n (n + k) (Nat.le_add_right n k) x)

/-- Any two fixed cofinal tails of the split Clifford tower are canonically
ring-equivalent, by transporting through the original direct limit. -/
noncomputable def splitCliffordTailInfinity_ring_shift_equiv (k l : ℕ) :
    SplitCliffordTailInfinity k ≃+* SplitCliffordTailInfinity l :=
  (splitCliffordInfinity_ring_shift_equiv k).symm.trans
    (splitCliffordInfinity_ring_shift_equiv l)

/-- The canonical equivalence between two cofinal tails intertwines their
induced Clifford grade involutions. -/
theorem splitCliffordTailInfinity_ring_shift_equiv_grade_involution
    (k l : ℕ) :
    (splitCliffordTailInfinityInvolute l).comp
        (splitCliffordTailInfinity_ring_shift_equiv k l).toRingHom =
      (splitCliffordTailInfinity_ring_shift_equiv k l).toRingHom.comp
        (splitCliffordTailInfinityInvolute k) := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext x
  simp only [RingHom.comp_apply, DirectLimit.Ring.lift_of,
    splitCliffordTailInfinityInvolute]
  change splitCliffordTailOf l (n + k)
      (CliffordAlgebra.involute (Q := Qsplit ((n + k) + l))
        (splitCliffordMap (n + k) ((n + k) + l)
          (Nat.le_add_right (n + k) l) x)) =
    splitCliffordTailOf l (n + k)
      (splitCliffordMap (n + k) ((n + k) + l)
        (Nat.le_add_right (n + k) l)
        (CliffordAlgebra.involute (Q := Qsplit (n + k)) x))
  exact congrArg (splitCliffordTailOf l (n + k))
    (splitCliffordMap_involute (n + k) ((n + k) + l)
      (Nat.le_add_right (n + k) l) x)

end InfoGeometry.Canonical.SplitCliffordDirectLimitRingShift

end
