/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitCliffordFiniteHeadTail
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import InfoGeometry.Clifford.Cl11Matrix

open scoped TensorProduct

/-!
# Fixed-head compatibility of the split Clifford tower

This bridge combines the finite head--tail Clifford factorization with the
existing canonical direct-limit stage transition. Its generator theorem records
how one recursive tower step is represented in the fixed head and enlarged
tail coordinates.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordHeadTailTower

open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordFiniteHeadTail
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.Cl11Matrix

/-- Concrete operator witness: the split-Clifford framework contains the
noncommuting `Cl(1,1)` matrix generators from its existing matrix owner. -/
theorem splitCliffordHeadTail_noncommutativity_witness :
    J1 * Eminus ≠ Eminus * J1 := J1_mul_Eminus_ne

/-- The canonical tail transition preserves each parity component. -/
private theorem splitCliffordStep_mem_evenOdd (n : ℕ) (p : ZMod 2)
    {x : CliffordAlgebra (Qsplit n)}
    (hx : x ∈ CliffordAlgebra.evenOdd (Qsplit n) p) :
    splitCliffordStep n x ∈ CliffordAlgebra.evenOdd (Qsplit (n + 1)) p := by
  have hmap := InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageCliffordMap_preserves_evenOdd
    n p (Submodule.mem_map_of_mem hx)
  change InfoGeometry.Algebra.SuperGrassmannianClifford.splitStageCliffordMap n x ∈ _ at hmap
  rw [InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.splitCliffordStep_eq_splitStageCliffordMap]
  exact hmap

/-- Fixed-head transition on the whole graded tensor-product algebra. -/
noncomputable def splitCliffordHeadTailStep (k n : ℕ) :
    (CliffordAlgebra.evenOdd (Qsplit k) ᵍ⊗[ℝ]
      CliffordAlgebra.evenOdd (Qsplit n)) →ₐ[ℝ]
      (CliffordAlgebra.evenOdd (Qsplit k) ᵍ⊗[ℝ]
        CliffordAlgebra.evenOdd (Qsplit (n + 1))) :=
  GradedTensorProduct.lift _ _
    (GradedTensorProduct.includeLeft
      (CliffordAlgebra.evenOdd (Qsplit k))
      (CliffordAlgebra.evenOdd (Qsplit (n + 1))))
    ((GradedTensorProduct.includeRight
      (CliffordAlgebra.evenOdd (Qsplit k))
      (CliffordAlgebra.evenOdd (Qsplit (n + 1)))).comp (splitCliffordStep n))
    (by
      intro i j a b
      let y := splitCliffordStep n (b : CliffordAlgebra (Qsplit n))
      have hy : y ∈ CliffordAlgebra.evenOdd (Qsplit (n + 1)) j :=
        splitCliffordStep_mem_evenOdd n j b.prop
      let uHead : CliffordAlgebra.evenOdd (Qsplit k) 0 := 1
      let uTail : CliffordAlgebra.evenOdd (Qsplit (n + 1)) 0 := 1
      let yGraded : CliffordAlgebra.evenOdd (Qsplit (n + 1)) j := ⟨y, hy⟩
      change ((a : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ (uTail : CliffordAlgebra (Qsplit (n + 1)))) *
          ((uHead : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ y) =
        (-1 : ℤˣ) ^ (j * i) •
          (((uHead : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ (yGraded : CliffordAlgebra (Qsplit (n + 1)))) *
            ((a : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ (uTail : CliffordAlgebra (Qsplit (n + 1)))) )
      rw [GradedTensorProduct.tmul_zero_coe_mul_coe_tmul,
        GradedTensorProduct.tmul_coe_mul_coe_tmul]
      simp [uHead, uTail, y, yGraded, smul_smul, Int.units_mul_self])

/-- On every pure tensor, the fixed-head map acts by the identity on the head
and by the canonical tower transition on the tail. -/
@[simp]
theorem splitCliffordHeadTailStep_tmul (k n : ℕ)
    (a : CliffordAlgebra (Qsplit k))
    (b : CliffordAlgebra (Qsplit n)) :
    splitCliffordHeadTailStep k n (a ᵍ⊗ₜ b) =
      GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit (n + 1))) a *
        GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit (n + 1)))
          (splitCliffordStep n b) := by
  simp [splitCliffordHeadTailStep, GradedTensorProduct.lift_tmul]

/-- After fixed-head factorization, the actual split-tower transition sends
each Clifford generator to its unchanged head component and its one-coordinate
tail inclusion. -/
theorem splitCliffordHeadTail_transition_generator (k n : ℕ)
    (x : SplitSpace (k + n)) :
    splitCliffordFiniteHeadTailEquiv k (n + 1)
        (splitCliffordStep (k + n)
          (CliffordAlgebra.ι (Qsplit (k + n)) x)) =
      (CliffordAlgebra.ι (Qsplit k)
        (splitSpaceAppendEquiv k n x).1)
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit (n + 1))) +
        (1 : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ
          CliffordAlgebra.ι (Qsplit (n + 1))
            (0, (splitSpaceAppendEquiv k n x).2) := by
  rw [InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.splitCliffordStep_eq_splitStageCliffordMap]
  rw [InfoGeometry.Clifford.ClNNSuperGrassmannianBridge.splitStageCliffordMap_generator_eq_gammaTail]
  rw [gammaTail]
  have htail : tailLift (k + n) x = (0, x) := by
    simp [tailLift]
  rw [htail]
  exact splitCliffordFiniteHeadTailEquiv_inr k n x

/-- The fixed-head graded tensor transition intertwines the finite Clifford
bonding map on the entire algebra, not only on generators. -/
theorem splitCliffordHeadTailStep_compatible (k n : ℕ) :
    (splitCliffordFiniteHeadTailEquiv k (n + 1)).toAlgHom.comp
        (splitCliffordStep (k + n)) =
      (splitCliffordHeadTailStep k n).comp
        (splitCliffordFiniteHeadTailEquiv k n).toAlgHom := by
  apply CliffordAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  change splitCliffordFiniteHeadTailEquiv k (n + 1)
      (splitCliffordStep (k + n) (CliffordAlgebra.ι (Qsplit (k + n)) x)) =
    splitCliffordHeadTailStep k n
      (splitCliffordFiniteHeadTailEquiv k n
        (CliffordAlgebra.ι (Qsplit (k + n)) x))
  rw [splitCliffordHeadTail_transition_generator]
  rw [splitCliffordFiniteHeadTailEquiv_ι]
  rw [map_add]
  rw [splitCliffordHeadTailStep_tmul, splitCliffordHeadTailStep_tmul]
  rw [InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.splitCliffordStep_eq_splitStageCliffordMap]
  rw [InfoGeometry.Clifford.ClNNSuperGrassmannianBridge.splitStageCliffordMap_generator_eq_gammaTail]
  have hleft (a : CliffordAlgebra (Qsplit k)) :
      GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit (n + 1))) a = a ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit (n + 1))) := rfl
  have hright (b : CliffordAlgebra (Qsplit (n + 1))) :
      GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit (n + 1))) b = (1 : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ b := rfl
  rw [hleft, hright (gammaTail n ((splitSpaceAppendEquiv k n x).2))]
  rw [map_one]
  rw [hright (1 : CliffordAlgebra (Qsplit (n + 1))),
    hleft (1 : CliffordAlgebra (Qsplit k))]
  rw [GradedTensorProduct.tmul_one_mul_one_tmul,
    GradedTensorProduct.tmul_one_mul_one_tmul]
  congr 2

/-- The `n`th fixed-head stage is the native graded tensor product of the
first `k` split coordinates and the remaining `n` coordinates. -/
abbrev SplitCliffordHeadTailStage (k n : ℕ) :=
  CliffordAlgebra.evenOdd (Qsplit k) ᵍ⊗[ℝ]
    CliffordAlgebra.evenOdd (Qsplit n)

/-- Transport an actual split-Clifford tower transition into fixed-head
coordinates. -/
noncomputable def splitCliffordHeadTailMap (k m n : ℕ) (h : m ≤ n) :
    SplitCliffordHeadTailStage k m →ₐ[ℝ]
      SplitCliffordHeadTailStage k n :=
  (splitCliffordFiniteHeadTailEquiv k n).toAlgHom.comp
    ((splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k)).comp
      (splitCliffordFiniteHeadTailEquiv k m).symm.toAlgHom)

/-- The transported bonds form a directed system because they are the actual
`Cl(n,n)` bonds conjugated by the finite head--tail algebra equivalences. -/
instance splitCliffordHeadTailDirectedSystem (k : ℕ) :
    DirectedSystem (SplitCliffordHeadTailStage k)
      (fun m n h => splitCliffordHeadTailMap k m n h) where
  map_self := by
    intro n x
    simp [splitCliffordHeadTailMap, splitCliffordMap_refl]
  map_map := by
    intro i j l hij hjl x
    change
      splitCliffordFiniteHeadTailEquiv k i
          (splitCliffordMap (k + j) (k + i)
            (Nat.add_le_add_left hjl k)
            ((splitCliffordFiniteHeadTailEquiv k j).symm
              (splitCliffordFiniteHeadTailEquiv k j
                (splitCliffordMap (k + l) (k + j)
                  (Nat.add_le_add_left hij k)
                  ((splitCliffordFiniteHeadTailEquiv k l).symm x))))) =
        splitCliffordFiniteHeadTailEquiv k i
          (splitCliffordMap (k + l) (k + i)
            (Nat.add_le_add_left (hij.trans hjl) k)
            ((splitCliffordFiniteHeadTailEquiv k l).symm x))
    simp only [AlgEquiv.symm_apply_apply]
    exact congrArg (splitCliffordFiniteHeadTailEquiv k i)
      (splitCliffordMap_apply_trans (k + l) (k + j) (k + i)
        (Nat.add_le_add_left hij k) (Nat.add_le_add_left hjl k)
        ((splitCliffordFiniteHeadTailEquiv k l).symm x)).symm

/-- Successor bonds in fixed-head coordinates agree with the directly
constructed graded-tensor transition. -/
theorem splitCliffordHeadTailMap_succ (k n : ℕ) :
    splitCliffordHeadTailMap k n (n + 1) (Nat.le_succ n) =
      splitCliffordHeadTailStep k n := by
  apply AlgHom.ext
  intro x
  change splitCliffordFiniteHeadTailEquiv k (n + 1)
      (splitCliffordMap (k + n) (k + (n + 1))
        (Nat.add_le_add_left (Nat.le_succ n) k)
        ((splitCliffordFiniteHeadTailEquiv k n).symm x)) = _
  have hmap :
      splitCliffordMap (k + n) (k + (n + 1))
        (Nat.add_le_add_left (Nat.le_succ n) k) =
      splitCliffordStep (k + n) := by
    have hproof : Nat.add_le_add_left (Nat.le_succ n) k =
        Nat.le_trans le_rfl (Nat.le_succ (k + n)) := Subsingleton.elim _ _
    simpa only [Nat.add_succ, Nat.add_zero, hproof,
      splitCliffordMap_refl, AlgHom.comp_id] using
      (splitCliffordMap_succ (k + n) (k + n) le_rfl)
  rw [hmap]
  simpa using AlgHom.congr_fun
    (splitCliffordHeadTailStep_compatible k n)
    ((splitCliffordFiniteHeadTailEquiv k n).symm x)

/-- Every transported head--tail transition is injective because the original
Clifford tower transition is injective and both coordinate changes are
algebra equivalences. -/
theorem splitCliffordHeadTailMap_injective (k m n : ℕ) (h : m ≤ n) :
    Function.Injective (splitCliffordHeadTailMap k m n h) := by
  intro x y hxy
  have hStage :
      splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k)
          ((splitCliffordFiniteHeadTailEquiv k m).symm x) =
        splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k)
          ((splitCliffordFiniteHeadTailEquiv k m).symm y) := by
    apply (splitCliffordFiniteHeadTailEquiv k n).injective
    simpa [splitCliffordHeadTailMap] using hxy
  have hSource :=
    (splitCliffordMap_injective (Nat.add_le_add_left h k)) hStage
  exact (splitCliffordFiniteHeadTailEquiv k m).symm.injective hSource

/-- Algebraic direct limit of the fixed-head graded tensor stages. -/
abbrev SplitCliffordHeadTailInfinity (k : ℕ) :=
  _root_.DirectLimit (SplitCliffordHeadTailStage k)
    (fun m n h => splitCliffordHeadTailMap k m n h)

/-- The canonical map from each fixed-head graded tensor stage to its direct
limit. -/
noncomputable def splitCliffordHeadTailOf (k n : ℕ) :
    SplitCliffordHeadTailStage k n →+*
      SplitCliffordHeadTailInfinity k :=
  DirectLimit.Ring.of (SplitCliffordHeadTailStage k)
    (fun m l h => (splitCliffordHeadTailMap k m l h).toRingHom) n

/-- Every finite fixed-head tensor stage embeds faithfully into its algebraic
direct limit. -/
theorem splitCliffordHeadTailInfinity_stage_injective (k n : ℕ) :
    Function.Injective (splitCliffordHeadTailOf k n) := by
  exact DirectLimit.mk_injective
    (f := fun i j h => splitCliffordHeadTailMap k i j h)
    (fun i j hij => splitCliffordHeadTailMap_injective k i j hij) n

end InfoGeometry.Canonical.SplitCliffordHeadTailTower

end
