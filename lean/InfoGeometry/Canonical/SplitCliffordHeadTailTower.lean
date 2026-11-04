/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitCliffordFiniteHeadTail
import InfoGeometry.Canonical.SplitCliffordDirectLimitRingShift
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import InfoGeometry.Clifford.Cl11Matrix
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

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
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
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

/-- The fixed-head successor transition is the ordinary module tensor of the
identity on the head with the Clifford successor map on the tail. -/
theorem splitCliffordHeadTailStep_toLinearMap (k n : ℕ) :
    (splitCliffordHeadTailStep k n).toLinearMap =
      LinearMap.lTensor (CliffordAlgebra (Qsplit k))
        (splitCliffordStep n) := by
  apply TensorProduct.ext'
  intro a b
  change splitCliffordHeadTailStep k n (a ᵍ⊗ₜ b) =
    a ⊗ₜ splitCliffordStep n b
  rw [splitCliffordHeadTailStep_tmul]
  have hleft :
      GradedTensorProduct.includeLeft
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit (n + 1))) a =
        a ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit (n + 1))) := rfl
  have hright :
      GradedTensorProduct.includeRight
          (CliffordAlgebra.evenOdd (Qsplit k))
          (CliffordAlgebra.evenOdd (Qsplit (n + 1)))
          (splitCliffordStep n b) =
        (1 : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ splitCliffordStep n b := rfl
  rw [hleft, hright, GradedTensorProduct.tmul_one_mul_one_tmul]
  rfl

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

/-- The actual transported tower successor is the tensor of the identity on
the fixed head with the canonical successor on the tail. -/
theorem splitCliffordHeadTailMap_succ_toLinearMap (k n : ℕ) :
    (splitCliffordHeadTailMap k n (n + 1) (Nat.le_succ n)).toLinearMap =
      LinearMap.lTensor (CliffordAlgebra (Qsplit k))
        (splitCliffordStep n) := by
  rw [splitCliffordHeadTailMap_succ,
    splitCliffordHeadTailStep_toLinearMap]

/-- Fixed-head interval bonds compose in the same order as the original
split-Clifford tower bonds. -/
theorem splitCliffordHeadTailMap_trans (k m n l : ℕ)
    (hmn : m ≤ n) (hnl : n ≤ l) :
    splitCliffordHeadTailMap k m l (hmn.trans hnl) =
      (splitCliffordHeadTailMap k n l hnl).comp
        (splitCliffordHeadTailMap k m n hmn) := by
  apply AlgHom.ext
  intro x
  change splitCliffordFiniteHeadTailEquiv k l
      (splitCliffordMap (k + m) (k + l) (Nat.add_le_add_left (hmn.trans hnl) k)
        ((splitCliffordFiniteHeadTailEquiv k m).symm x)) =
    splitCliffordFiniteHeadTailEquiv k l
      (splitCliffordMap (k + n) (k + l) (Nat.add_le_add_left hnl k)
        ((splitCliffordFiniteHeadTailEquiv k n).symm
          (splitCliffordFiniteHeadTailEquiv k n
            (splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left hmn k)
              ((splitCliffordFiniteHeadTailEquiv k m).symm x)))))
  simp only [AlgEquiv.symm_apply_apply]
  exact congrArg (splitCliffordFiniteHeadTailEquiv k l)
    (splitCliffordMap_apply_trans (k + m) (k + n) (k + l)
      (Nat.add_le_add_left hmn k) (Nat.add_le_add_left hnl k)
      ((splitCliffordFiniteHeadTailEquiv k m).symm x))

/-- The fixed-head algebra tower is also a directed system of real modules
through the underlying maps of its algebra bonds. -/
instance splitCliffordHeadTailModuleDirectedSystem (k : ℕ) :
    DirectedSystem (SplitCliffordHeadTailStage k)
      (fun m n h => (splitCliffordHeadTailMap k m n h).toLinearMap) where
  map_self := by
    intro n x
    change splitCliffordHeadTailMap k n n le_rfl x = x
    simp [splitCliffordHeadTailMap, splitCliffordMap_refl]
  map_map := by
    intro i j l hij hjl x
    simpa using (congrArg (fun f : SplitCliffordHeadTailStage k l →ₐ[ℝ]
        SplitCliffordHeadTailStage k i => f x)
      (splitCliffordHeadTailMap_trans k l j i hij hjl)).symm

/-- Every fixed-head interval bond is the ordinary module tensor of the
identity on the head with the canonical Clifford interval bond on the tail.
This identifies the whole transported tower with Mathlib's right-tensor
direct-limit system, rather than only identifying its successors. -/
theorem splitCliffordHeadTailMap_toLinearMap (k m n : ℕ) (h : m ≤ n) :
    (splitCliffordHeadTailMap k m n h).toLinearMap =
      LinearMap.lTensor (CliffordAlgebra (Qsplit k))
        (splitCliffordMap m n h).toLinearMap := by
  induction n, h using Nat.le_induction with
  | base =>
      simp [splitCliffordHeadTailMap, splitCliffordMap_refl]
      rfl
  | succ n hmn ih =>
      rw [splitCliffordHeadTailMap_trans k m n (n + 1) hmn (Nat.le_succ n)]
      rw [AlgHom.comp_toLinearMap,
        splitCliffordHeadTailMap_succ_toLinearMap, ih]
      rw [splitCliffordMap_succ]
      exact (LinearMap.lTensor_comp
        (M := CliffordAlgebra (Qsplit k))
        (f := (splitCliffordMap m n hmn).toLinearMap)
        (g := (splitCliffordStep n).toLinearMap)).symm

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

private abbrev SplitCliffordInfinityModuleLimit :=
  Module.DirectLimit SplitClNNAlg
    (fun m n h => (splitCliffordMap m n h).toLinearMap)

private abbrev SplitCliffordHeadTailModuleLimit (k : ℕ) :=
  Module.DirectLimit (SplitCliffordHeadTailStage k)
    (fun m n h => (splitCliffordHeadTailMap k m n h).toLinearMap)

private noncomputable def splitCliffordInfinityToModuleLimit :
    SplitCliffordInfinity →ₗ[ℝ] SplitCliffordInfinityModuleLimit :=
  DirectLimit.Module.lift ℝ ℕ SplitClNNAlg
    (fun m n h => splitCliffordMap m n h)
    (fun n => Module.DirectLimit.of ℝ ℕ SplitClNNAlg
      (fun m n h => (splitCliffordMap m n h).toLinearMap) n)
    (by
      intro m n h x
      change Module.DirectLimit.of ℝ ℕ SplitClNNAlg
          (fun i j hij => (splitCliffordMap i j hij).toLinearMap) n
          (splitCliffordMap m n h x) =
        Module.DirectLimit.of ℝ ℕ SplitClNNAlg
          (fun i j hij => (splitCliffordMap i j hij).toLinearMap) m x
      exact Module.DirectLimit.of_f
        (R := ℝ) (ι := ℕ) (G := SplitClNNAlg)
        (f := fun i j hij => (splitCliffordMap i j hij).toLinearMap)
        (hij := h) (x := x))

private noncomputable def splitCliffordModuleLimitToInfinity :
    SplitCliffordInfinityModuleLimit →ₗ[ℝ] SplitCliffordInfinity :=
  Module.DirectLimit.lift ℝ ℕ SplitClNNAlg
    (fun m n h => (splitCliffordMap m n h).toLinearMap)
    (fun n => DirectLimit.Module.of ℝ ℕ SplitClNNAlg
      (fun m n h => splitCliffordMap m n h) n)
    (by
      intro m n h x
      change DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) n
          (splitCliffordMap m n h x) =
        DirectLimit.Module.of ℝ ℕ SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) m x
      exact DirectLimit.Module.of_f
        (G := SplitClNNAlg)
        (f := fun i j hij => splitCliffordMap i j hij)
        (hij := h) (x := x))

/-- The explicit directed-system quotient and Mathlib's universal module
direct limit of the split-Clifford tower are canonically linearly equivalent.
The maps are induced by the same finite-stage inclusions in both directions. -/
noncomputable def splitCliffordInfinity_moduleEquiv :
    SplitCliffordInfinity ≃ₗ[ℝ] SplitCliffordInfinityModuleLimit := by
  refine LinearEquiv.ofLinearMap splitCliffordInfinityToModuleLimit
    splitCliffordModuleLimitToInfinity ?_ ?_
  · apply Module.DirectLimit.hom_ext
    intro n
    apply LinearMap.ext
    intro x
    change splitCliffordInfinityToModuleLimit
        (splitCliffordModuleLimitToInfinity
          (Module.DirectLimit.of ℝ ℕ SplitClNNAlg
            (fun i j h => (splitCliffordMap i j h).toLinearMap) n x)) = _
    rw [splitCliffordModuleLimitToInfinity, Module.DirectLimit.lift_of,
      splitCliffordInfinityToModuleLimit, DirectLimit.Module.lift_of]
    rfl
  · apply DirectLimit.Module.hom_ext
    intro n
    apply LinearMap.ext
    intro x
    change splitCliffordModuleLimitToInfinity
        (splitCliffordInfinityToModuleLimit
          (DirectLimit.Module.of ℝ ℕ SplitClNNAlg
            (fun i j h => splitCliffordMap i j h) n x)) = _
    rw [splitCliffordInfinityToModuleLimit, DirectLimit.Module.lift_of,
      splitCliffordModuleLimitToInfinity, Module.DirectLimit.lift_of]
    rfl

private noncomputable def splitCliffordHeadTailToModuleLimit (k : ℕ) :
    SplitCliffordHeadTailInfinity k →ₗ[ℝ]
      SplitCliffordHeadTailModuleLimit k :=
  DirectLimit.Module.lift ℝ ℕ (SplitCliffordHeadTailStage k)
    (fun m n h => splitCliffordHeadTailMap k m n h)
    (fun n => Module.DirectLimit.of ℝ ℕ (SplitCliffordHeadTailStage k)
      (fun m n h => (splitCliffordHeadTailMap k m n h).toLinearMap) n)
    (by
      intro m n h x
      change Module.DirectLimit.of ℝ ℕ (SplitCliffordHeadTailStage k)
          (fun i j hij => (splitCliffordHeadTailMap k i j hij).toLinearMap) n
          (splitCliffordHeadTailMap k m n h x) =
        Module.DirectLimit.of ℝ ℕ (SplitCliffordHeadTailStage k)
          (fun i j hij => (splitCliffordHeadTailMap k i j hij).toLinearMap) m x
      exact Module.DirectLimit.of_f
        (R := ℝ) (ι := ℕ) (G := SplitCliffordHeadTailStage k)
        (f := fun i j hij => (splitCliffordHeadTailMap k i j hij).toLinearMap)
        (hij := h) (x := x))

private noncomputable def splitCliffordModuleLimitToHeadTail (k : ℕ) :
    SplitCliffordHeadTailModuleLimit k →ₗ[ℝ]
      SplitCliffordHeadTailInfinity k :=
  Module.DirectLimit.lift ℝ ℕ (SplitCliffordHeadTailStage k)
    (fun m n h => (splitCliffordHeadTailMap k m n h).toLinearMap)
    (fun n => DirectLimit.Module.of ℝ ℕ (SplitCliffordHeadTailStage k)
      (fun m n h => splitCliffordHeadTailMap k m n h) n)
    (by
      intro m n h x
      change DirectLimit.Module.of ℝ ℕ (SplitCliffordHeadTailStage k)
          (fun i j hij => splitCliffordHeadTailMap k i j hij) n
          (splitCliffordHeadTailMap k m n h x) =
        DirectLimit.Module.of ℝ ℕ (SplitCliffordHeadTailStage k)
          (fun i j hij => splitCliffordHeadTailMap k i j hij) m x
      exact DirectLimit.Module.of_f
        (G := SplitCliffordHeadTailStage k)
        (f := fun i j hij => splitCliffordHeadTailMap k i j hij)
        (hij := h) (x := x))

private noncomputable def splitCliffordHeadTailInfinity_moduleEquiv (k : ℕ) :
    SplitCliffordHeadTailInfinity k ≃ₗ[ℝ]
      SplitCliffordHeadTailModuleLimit k := by
  refine LinearEquiv.ofLinearMap (splitCliffordHeadTailToModuleLimit k)
    (splitCliffordModuleLimitToHeadTail k) ?_ ?_
  · apply Module.DirectLimit.hom_ext
    intro n
    apply LinearMap.ext
    intro x
    change splitCliffordHeadTailToModuleLimit k
        (splitCliffordModuleLimitToHeadTail k
          (Module.DirectLimit.of ℝ ℕ (SplitCliffordHeadTailStage k)
            (fun i j h => (splitCliffordHeadTailMap k i j h).toLinearMap) n x)) = _
    rw [splitCliffordModuleLimitToHeadTail, Module.DirectLimit.lift_of,
      splitCliffordHeadTailToModuleLimit, DirectLimit.Module.lift_of]
    rfl
  · apply DirectLimit.Module.hom_ext
    intro n
    apply LinearMap.ext
    intro x
    change splitCliffordModuleLimitToHeadTail k
        (splitCliffordHeadTailToModuleLimit k
          (DirectLimit.Module.of ℝ ℕ (SplitCliffordHeadTailStage k)
            (fun i j h => splitCliffordHeadTailMap k i j h) n x)) = _
    rw [splitCliffordHeadTailToModuleLimit, DirectLimit.Module.lift_of,
      splitCliffordModuleLimitToHeadTail, Module.DirectLimit.lift_of]
    rfl

/-- As modules, the fixed-head colimit is the tensor product of the head with
the original split-Clifford colimit. This uses the interval-bond identity
above and Mathlib's tensor/direct-limit equivalence; multiplicativity is not
part of this linear equivalence. -/
private noncomputable def splitCliffordHeadTailModuleLimitEquiv (k : ℕ) :
    CliffordAlgebra (Qsplit k) ⊗[ℝ]
        Module.DirectLimit SplitClNNAlg
          (fun m n h => (splitCliffordMap m n h).toLinearMap) ≃ₗ[ℝ]
      SplitCliffordHeadTailModuleLimit k := by
  let tailBond (m n : ℕ) (h : m ≤ n) :
      SplitClNNAlg m →ₗ[ℝ] SplitClNNAlg n :=
    (splitCliffordMap m n h).toLinearMap
  let fixedHeadBond (m n : ℕ) (h : m ≤ n) :
      SplitCliffordHeadTailStage k m →ₗ[ℝ]
        SplitCliffordHeadTailStage k n :=
    (splitCliffordHeadTailMap k m n h).toLinearMap
  let tensorLimit := TensorProduct.directLimitRight tailBond
    (CliffordAlgebra (Qsplit k))
  let stageEquiv (n : ℕ) :
      (CliffordAlgebra (Qsplit k) ⊗[ℝ] SplitClNNAlg n) ≃ₗ[ℝ]
        SplitCliffordHeadTailStage k n :=
    GradedTensorProduct.of ℝ
      (CliffordAlgebra.evenOdd (Qsplit k))
      (CliffordAlgebra.evenOdd (Qsplit n))
  let limitEquiv := Module.DirectLimit.congr stageEquiv
    (by
      intro m n h
      change (LinearMap.id : _ →ₗ[ℝ] _) ∘ₗ
          LinearMap.lTensor (CliffordAlgebra (Qsplit k)) (tailBond m n h) =
        fixedHeadBond m n h ∘ₗ (LinearMap.id : _ →ₗ[ℝ] _)
      rw [LinearMap.id_comp, LinearMap.comp_id]
      exact (splitCliffordHeadTailMap_toLinearMap k m n h).symm)
  simpa [tailBond, fixedHeadBond] using tensorLimit.trans limitEquiv

/-- The fixed-head ring colimit is linearly equivalent to the tensor product
of its finite Clifford head with the repository's split-Clifford ring
colimit. The construction uses Mathlib's tensor/direct-limit equivalence and
the canonical linear equivalences between the two direct-limit
presentations. This statement does not assert multiplicativity for the
ordinary tensor product. -/
noncomputable def splitCliffordHeadTailModuleEquiv (k : ℕ) :
    CliffordAlgebra (Qsplit k) ⊗[ℝ] SplitCliffordInfinity ≃ₗ[ℝ]
      SplitCliffordHeadTailInfinity k := by
  let headEquiv : CliffordAlgebra (Qsplit k) ≃ₗ[ℝ]
      CliffordAlgebra (Qsplit k) := LinearEquiv.refl ℝ _
  exact (TensorProduct.congr headEquiv (splitCliffordInfinity_moduleEquiv)).trans
    ((splitCliffordHeadTailModuleLimitEquiv k).trans
      (splitCliffordHeadTailInfinity_moduleEquiv k).symm)

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

/-- Canonical finite-stage maps for the original split-Clifford limit. -/
private noncomputable def splitCliffordInfinityOf (n : ℕ) :
    SplitClNNAlg n →+* SplitCliffordInfinity :=
  (DirectLimit.Algebra.of SplitClNNAlg
    (fun i j h => splitCliffordMap i j h) n).toRingHom

private theorem splitCliffordTailOf_zero_eq_infinityOf (n : ℕ)
    (x : SplitClNNAlg (n + 0)) :
    InfoGeometry.Canonical.SplitCliffordDirectLimitRingShift.splitCliffordTailOf
        0 n x = splitCliffordInfinityOf n x := by
  rfl

private theorem splitCliffordInfinity_moduleEquiv_infinityOf (n : ℕ)
    (x : SplitClNNAlg n) :
    splitCliffordInfinity_moduleEquiv (splitCliffordInfinityOf n x) =
      Module.DirectLimit.of ℝ ℕ SplitClNNAlg
        (fun i j h => (splitCliffordMap i j h).toLinearMap) n x := by
  change splitCliffordInfinityToModuleLimit
      (splitCliffordInfinityOf n x) = _
  rw [splitCliffordInfinityToModuleLimit, splitCliffordInfinityOf]
  rfl

/-- The fixed-head module equivalence agrees with the graded stage inclusion
on a tensor whose tail component comes from a finite Clifford stage. -/
theorem splitCliffordHeadTailModuleEquiv_tmul_ofStage
    (k n : ℕ) (a : CliffordAlgebra (Qsplit k))
    (x : SplitClNNAlg n) :
    splitCliffordHeadTailModuleEquiv k
        (a ⊗ₜ[ℝ]
          InfoGeometry.Canonical.SplitCliffordDirectLimitRingShift.splitCliffordTailOf
            0 n x) =
      splitCliffordHeadTailOf k n (a ᵍ⊗ₜ x) := by
  rw [splitCliffordTailOf_zero_eq_infinityOf]
  simp only [splitCliffordHeadTailModuleEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rw [splitCliffordInfinity_moduleEquiv_infinityOf]
  simp [splitCliffordHeadTailModuleLimitEquiv,
    splitCliffordHeadTailInfinity_moduleEquiv,
    splitCliffordHeadTailToModuleLimit,
    splitCliffordModuleLimitToHeadTail,
    splitCliffordHeadTailOf,
    TensorProduct.directLimitRight_tmul_of,
    Module.DirectLimit.congr_apply_of,
    Module.DirectLimit.lift_of]
  rfl

/-- Map the fixed-head graded-tensor direct limit to the original Clifford
direct limit by the finite head--tail equivalences. -/
noncomputable def splitCliffordHeadTailToInfinity (k : ℕ) :
    SplitCliffordHeadTailInfinity k →+* SplitCliffordInfinity :=
  DirectLimit.Ring.lift (SplitCliffordHeadTailStage k)
    (fun m n h => (splitCliffordHeadTailMap k m n h).toRingHom)
    SplitCliffordInfinity
    (fun n => (splitCliffordInfinityOf (k + n)).comp
      (splitCliffordFiniteHeadTailEquiv k n).symm.toAlgHom.toRingHom)
    (by
      intro m n h x
      simp only [RingHom.comp_apply, splitCliffordHeadTailMap]
      change splitCliffordInfinityOf (k + n)
          ((splitCliffordFiniteHeadTailEquiv k n).symm
            (splitCliffordFiniteHeadTailEquiv k n
              (splitCliffordMap (k + m) (k + n)
                (Nat.add_le_add_left h k)
                ((splitCliffordFiniteHeadTailEquiv k m).symm x)))) = _
      rw [AlgEquiv.symm_apply_apply]
      exact DirectLimit.Ring.of_f
        (G := SplitClNNAlg)
        (f := fun i j hij => (splitCliffordMap i j hij).toRingHom)
        (hij := Nat.add_le_add_left h k)
        (x := (splitCliffordFiniteHeadTailEquiv k m).symm x))

/-- On a finite fixed-head stage, the induced map is the finite algebra
equivalence followed by the canonical map from stage `k+n`. -/
@[simp]
theorem splitCliffordHeadTailToInfinity_of (k n : ℕ)
    (x : SplitCliffordHeadTailStage k n) :
    splitCliffordHeadTailToInfinity k (splitCliffordHeadTailOf k n x) =
      splitCliffordInfinityOf (k + n)
        ((splitCliffordFiniteHeadTailEquiv k n).symm x) := by
  change DirectLimit.Ring.lift (SplitCliffordHeadTailStage k)
      (fun m l h => (splitCliffordHeadTailMap k m l h).toRingHom)
      SplitCliffordInfinity
      (fun j => (splitCliffordInfinityOf (k + j)).comp
        (splitCliffordFiniteHeadTailEquiv k j).symm.toAlgHom.toRingHom) _
      (DirectLimit.Ring.of (SplitCliffordHeadTailStage k)
        (fun i j h => (splitCliffordHeadTailMap k i j h).toRingHom) n x) = _
  rw [DirectLimit.Ring.lift_of]
  rfl

/-- The reverse finite-stage map adds the fixed head to the original tower
stage and then applies the finite head--tail algebra equivalence. -/
private noncomputable def splitCliffordInfinityIntoHeadTailAlgHom
    (k n : ℕ) : SplitClNNAlg n →ₐ[ℝ] SplitCliffordHeadTailStage k n :=
  (splitCliffordFiniteHeadTailEquiv k n).toAlgHom.comp
    (splitCliffordMap n (k + n) (Nat.le_add_left n k))

/-- The reverse finite-stage maps intertwine the original tower transitions
with the transported fixed-head transitions. -/
private theorem splitCliffordInfinityIntoHeadTailAlgHom_natural
    (k m n : ℕ) (h : m ≤ n) :
    (splitCliffordHeadTailMap k m n h).comp
        (splitCliffordInfinityIntoHeadTailAlgHom k m) =
      (splitCliffordInfinityIntoHeadTailAlgHom k n).comp
        (splitCliffordMap m n h) := by
  apply AlgHom.ext
  intro x
  change splitCliffordFiniteHeadTailEquiv k n
      (splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k)
        ((splitCliffordFiniteHeadTailEquiv k m).symm
          (splitCliffordFiniteHeadTailEquiv k m
            (splitCliffordMap m (k + m) (Nat.le_add_left m k) x)))) =
    splitCliffordFiniteHeadTailEquiv k n
      (splitCliffordMap n (k + n) (Nat.le_add_left n k)
        (splitCliffordMap m n h x))
  rw [AlgEquiv.symm_apply_apply]
  congr 1
  calc
    splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k)
        (splitCliffordMap m (k + m) (Nat.le_add_left m k) x) =
      splitCliffordMap m (k + n)
        ((Nat.le_add_left m k).trans (Nat.add_le_add_left h k)) x :=
          (splitCliffordMap_apply_trans m (k + m) (k + n)
            (Nat.le_add_left m k) (Nat.add_le_add_left h k) x).symm
    _ = splitCliffordMap n (k + n) (Nat.le_add_left n k)
        (splitCliffordMap m n h x) := by
          rw [splitCliffordMap_apply_trans m n (k + n) h
            (Nat.le_add_left n k)]

/-- The canonical stage maps induce a ring hom from the original limit to
the fixed-head graded-tensor limit. -/
noncomputable def splitCliffordInfinityToHeadTail (k : ℕ) :
    SplitCliffordInfinity →+* SplitCliffordHeadTailInfinity k :=
  DirectLimit.Ring.lift SplitClNNAlg
    (fun m n h => (splitCliffordMap m n h).toRingHom)
    (SplitCliffordHeadTailInfinity k)
    (fun n => (splitCliffordHeadTailOf k n).comp
      (splitCliffordInfinityIntoHeadTailAlgHom k n).toRingHom)
    (by
      intro m n h x
      have hn := congrArg (fun f : SplitClNNAlg m →ₐ[ℝ]
          SplitCliffordHeadTailStage k n => f x)
        (splitCliffordInfinityIntoHeadTailAlgHom_natural k m n h).symm
      rw [AlgHom.comp_apply] at hn
      calc
        splitCliffordHeadTailOf k n
            (splitCliffordInfinityIntoHeadTailAlgHom k n
              (splitCliffordMap m n h x)) =
          splitCliffordHeadTailOf k n
            (splitCliffordHeadTailMap k m n h
              (splitCliffordInfinityIntoHeadTailAlgHom k m x)) := by
                exact congrArg (splitCliffordHeadTailOf k n) hn
        _ = splitCliffordHeadTailOf k m
            (splitCliffordInfinityIntoHeadTailAlgHom k m x) :=
              DirectLimit.Ring.of_f
                (G := SplitCliffordHeadTailStage k)
                (f := fun i j hij => (splitCliffordHeadTailMap k i j hij).toRingHom)
                (hij := h) (x := splitCliffordInfinityIntoHeadTailAlgHom k m x))

/-- On a finite original stage, the reverse limit map is the canonical
fixed-head stage map after adjoining the chosen finite head. -/
@[simp]
theorem splitCliffordInfinityToHeadTail_of (k n : ℕ)
    (x : SplitClNNAlg n) :
    splitCliffordInfinityToHeadTail k (splitCliffordInfinityOf n x) =
      splitCliffordHeadTailOf k n
        (splitCliffordInfinityIntoHeadTailAlgHom k n x) := by
  change DirectLimit.Ring.lift SplitClNNAlg
      (fun i j h => (splitCliffordMap i j h).toRingHom)
      (SplitCliffordHeadTailInfinity k)
      (fun j => (splitCliffordHeadTailOf k j).comp
        (splitCliffordInfinityIntoHeadTailAlgHom k j).toRingHom) _
      (DirectLimit.Ring.of SplitClNNAlg
        (fun i j h => (splitCliffordMap i j h).toRingHom) n x) = _
  rw [DirectLimit.Ring.lift_of]
  rfl

/-- The two comparison maps compose to the identity on each fixed-head stage
in the direct limit. -/
private theorem splitCliffordHeadTail_roundTrip_of (k n : ℕ)
    (x : SplitCliffordHeadTailStage k n) :
    splitCliffordInfinityToHeadTail k
        (splitCliffordHeadTailToInfinity k (splitCliffordHeadTailOf k n x)) =
      splitCliffordHeadTailOf k n x := by
  rw [splitCliffordHeadTailToInfinity_of,
    splitCliffordInfinityToHeadTail_of]
  change splitCliffordHeadTailOf k (k + n)
      (splitCliffordHeadTailMap k n (k + n) (Nat.le_add_left n k) x) = _
  exact DirectLimit.Ring.of_f
    (G := SplitCliffordHeadTailStage k)
    (f := fun i j h => (splitCliffordHeadTailMap k i j h).toRingHom)
    (hij := Nat.le_add_left n k) x

/-- The two comparison maps compose to the identity on each original
finite Clifford stage in the direct limit. -/
private theorem splitCliffordInfinity_roundTrip_of (k n : ℕ)
    (x : SplitClNNAlg n) :
    splitCliffordHeadTailToInfinity k
        (splitCliffordInfinityToHeadTail k (splitCliffordInfinityOf n x)) =
      splitCliffordInfinityOf n x := by
  rw [splitCliffordInfinityToHeadTail_of,
    splitCliffordHeadTailToInfinity_of]
  change splitCliffordInfinityOf (k + n)
      ((splitCliffordFiniteHeadTailEquiv k n).symm
        (splitCliffordFiniteHeadTailEquiv k n
          (splitCliffordMap n (k + n) (Nat.le_add_left n k) x))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact DirectLimit.Ring.of_f
    (G := SplitClNNAlg)
    (f := fun i j h => (splitCliffordMap i j h).toRingHom)
    (hij := Nat.le_add_left n k) x

/-- Fixed-head factorization induces a ring equivalence between its graded
tensor direct limit and the original algebraic split-Clifford direct limit. -/
noncomputable def splitCliffordHeadTailInfinity_ringEquiv (k : ℕ) :
    SplitCliffordHeadTailInfinity k ≃+* SplitCliffordInfinity :=
  RingEquiv.ofRingHom (splitCliffordHeadTailToInfinity k)
    (splitCliffordInfinityToHeadTail k)
    (by
      apply DirectLimit.Ring.hom_ext
      intro n
      ext x
      exact splitCliffordInfinity_roundTrip_of k n x)
    (by
      apply DirectLimit.Ring.hom_ext
      intro n
      ext x
      exact splitCliffordHeadTail_roundTrip_of k n x)

/-- The fixed-head ring equivalence preserves the canonical real scalar maps,
so the head--tail identification is an equivalence of real algebras. -/
theorem splitCliffordHeadTailInfinity_ringEquiv_commutes (k : ℕ) (r : ℝ) :
    splitCliffordHeadTailInfinity_ringEquiv k
        (algebraMap ℝ (SplitCliffordHeadTailInfinity k) r) =
      algebraMap ℝ SplitCliffordInfinity r := by
  rw [DirectLimit.algebraMap_def
        (G := SplitCliffordHeadTailStage k)
        (f := fun i j h => splitCliffordHeadTailMap k i j h) 0 r,
      DirectLimit.algebraMap_def
        (G := SplitClNNAlg)
        (f := fun i j h => splitCliffordMap i j h) k r]
  change splitCliffordHeadTailToInfinity k
      (splitCliffordHeadTailOf k 0
        (algebraMap ℝ (SplitCliffordHeadTailStage k 0) r)) =
    splitCliffordInfinityOf k (algebraMap ℝ (SplitClNNAlg k) r)
  rw [splitCliffordHeadTailToInfinity_of]
  congr 1
  exact (splitCliffordFiniteHeadTailEquiv k 0).symm.commutes r

/-- The fixed-head ring identification is an `ℝ`-algebra equivalence. -/
noncomputable def splitCliffordHeadTailInfinity_algEquiv (k : ℕ) :
    SplitCliffordHeadTailInfinity k ≃ₐ[ℝ] SplitCliffordInfinity :=
  AlgEquiv.ofRingEquiv (f := splitCliffordHeadTailInfinity_ringEquiv k)
    (splitCliffordHeadTailInfinity_ringEquiv_commutes k)

/-- The finite Clifford grade involution transported to a fixed-head graded
tensor stage, viewed as an endomorphism of its underlying algebra. -/
noncomputable def splitCliffordHeadTailStageInvolute (k n : ℕ) :
    SplitCliffordHeadTailStage k n →ₐ[ℝ] SplitCliffordHeadTailStage k n :=
  ((splitCliffordFiniteHeadTailEquiv k n).toAlgHom.comp
    (CliffordAlgebra.involute (Q := Qsplit (k + n)))).comp
      (splitCliffordFiniteHeadTailEquiv k n).symm.toAlgHom

/-- The finite transported grade involution is real-linear. -/
theorem splitCliffordHeadTailStageInvolute_smul (k n : ℕ) (r : ℝ)
    (x : SplitCliffordHeadTailStage k n) :
    splitCliffordHeadTailStageInvolute k n (r • x) =
      r • splitCliffordHeadTailStageInvolute k n x := by
  exact map_smul (splitCliffordHeadTailStageInvolute k n) r x

/-- The transported stage involutions commute with fixed-head transitions,
since those transitions are conjugates of the original split-Clifford bonds. -/
theorem splitCliffordHeadTailMap_involute (k m n : ℕ) (h : m ≤ n) :
    (splitCliffordHeadTailMap k m n h).comp
        (splitCliffordHeadTailStageInvolute k m) =
      (splitCliffordHeadTailStageInvolute k n).comp
        (splitCliffordHeadTailMap k m n h) := by
  apply AlgHom.ext
  intro x
  let Eₘ := splitCliffordFiniteHeadTailEquiv k m
  let Eₙ := splitCliffordFiniteHeadTailEquiv k n
  change Eₙ ((splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k))
      (Eₘ.symm (Eₘ (CliffordAlgebra.involute (Eₘ.symm x))))) =
    Eₙ (CliffordAlgebra.involute (Eₙ.symm (Eₙ
      ((splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k))
        (Eₘ.symm x)))))
  calc
    Eₙ ((splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k))
        (Eₘ.symm (Eₘ (CliffordAlgebra.involute (Eₘ.symm x))))) =
      Eₙ ((splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k))
        (CliffordAlgebra.involute (Eₘ.symm x))) := by
          congr 2
          exact Eₘ.symm_apply_apply _
    _ = Eₙ (CliffordAlgebra.involute
          ((splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k))
            (Eₘ.symm x))) := by
          exact congrArg Eₙ
            (splitCliffordMap_involute (k + m) (k + n)
              (Nat.add_le_add_left h k) (Eₘ.symm x)).symm
    _ = Eₙ (CliffordAlgebra.involute (Eₙ.symm (Eₙ
          ((splitCliffordMap (k + m) (k + n) (Nat.add_le_add_left h k))
            (Eₘ.symm x))))) := by
          congr 2
          exact (Eₙ.symm_apply_apply _).symm

/-- The stagewise Clifford grade involutions induce an involution on the
fixed-head graded-tensor algebraic direct limit. -/
noncomputable def splitCliffordHeadTailInfinityInvolute (k : ℕ) :
    SplitCliffordHeadTailInfinity k →+* SplitCliffordHeadTailInfinity k :=
  DirectLimit.Ring.lift (SplitCliffordHeadTailStage k)
    (fun m n h => (splitCliffordHeadTailMap k m n h).toRingHom)
    (SplitCliffordHeadTailInfinity k)
    (fun n => (splitCliffordHeadTailOf k n).comp
      (splitCliffordHeadTailStageInvolute k n).toRingHom)
    (by
      intro m n h x
      calc
        splitCliffordHeadTailOf k n
            (splitCliffordHeadTailStageInvolute k n
              (splitCliffordHeadTailMap k m n h x)) =
          splitCliffordHeadTailOf k n
            (splitCliffordHeadTailMap k m n h
              (splitCliffordHeadTailStageInvolute k m x)) := by
                exact congrArg (splitCliffordHeadTailOf k n)
                  (AlgHom.congr_fun
                    (splitCliffordHeadTailMap_involute k m n h).symm x)
        _ = splitCliffordHeadTailOf k m
              (splitCliffordHeadTailStageInvolute k m x) :=
                DirectLimit.Ring.of_f
                  (G := SplitCliffordHeadTailStage k)
                  (f := fun i j hij => (splitCliffordHeadTailMap k i j hij).toRingHom)
                  (hij := h) (x := splitCliffordHeadTailStageInvolute k m x))

@[simp] theorem splitCliffordHeadTailInfinityInvolute_ofStage
    (k n : ℕ) (x : SplitCliffordHeadTailStage k n) :
    splitCliffordHeadTailInfinityInvolute k (splitCliffordHeadTailOf k n x) =
      splitCliffordHeadTailOf k n
        (splitCliffordHeadTailStageInvolute k n x) := by
  change DirectLimit.Ring.lift (SplitCliffordHeadTailStage k)
      (fun m n h => (splitCliffordHeadTailMap k m n h).toRingHom)
      (SplitCliffordHeadTailInfinity k)
      (fun n => (splitCliffordHeadTailOf k n).comp
        (splitCliffordHeadTailStageInvolute k n).toRingHom) _
      (DirectLimit.Ring.of (SplitCliffordHeadTailStage k)
        (fun m n h => (splitCliffordHeadTailMap k m n h).toRingHom) n x) = _
  rw [DirectLimit.Ring.lift_of]
  rfl

/-- The induced grading involution on the fixed-head direct limit is
involutive. -/
theorem splitCliffordHeadTailInfinityInvolute_involutive (k : ℕ)
    (x : SplitCliffordHeadTailInfinity k) :
    splitCliffordHeadTailInfinityInvolute k
        (splitCliffordHeadTailInfinityInvolute k x) = x := by
  induction x using DirectLimit.induction with
  | _ n a =>
      change splitCliffordHeadTailInfinityInvolute k
          (splitCliffordHeadTailInfinityInvolute k
            (splitCliffordHeadTailOf k n a)) = _
      rw [splitCliffordHeadTailInfinityInvolute_ofStage,
        splitCliffordHeadTailInfinityInvolute_ofStage]
      exact congrArg (splitCliffordHeadTailOf k n) (by
        simp [splitCliffordHeadTailStageInvolute,
          CliffordAlgebra.involute_involute])

/-- The fixed-head limit involution agrees under the head--tail ring
equivalence with the canonical involution on the split-Clifford limit. -/
theorem splitCliffordHeadTailInfinity_ringEquiv_grade_involution (k : ℕ) :
    (InfoGeometry.Canonical.SplitCliffordSuperGradeColimit.splitCliffordInfinityInvolute.toRingHom).comp
        (splitCliffordHeadTailInfinity_ringEquiv k).toRingHom =
      (splitCliffordHeadTailInfinity_ringEquiv k).toRingHom.comp
        (splitCliffordHeadTailInfinityInvolute k) := by
  apply DirectLimit.Ring.hom_ext
  intro n
  ext x
  change InfoGeometry.Canonical.SplitCliffordSuperGradeColimit.splitCliffordInfinityInvolute
      (splitCliffordHeadTailToInfinity k (splitCliffordHeadTailOf k n x)) =
    splitCliffordHeadTailToInfinity k
      (splitCliffordHeadTailInfinityInvolute k (splitCliffordHeadTailOf k n x))
  change splitCliffordInfinityInvolute
      (DirectLimit.Algebra.of SplitClNNAlg
        (fun i j hij => splitCliffordMap i j hij) (k + n)
        ((splitCliffordFiniteHeadTailEquiv k n).symm x)) =
    splitCliffordHeadTailToInfinity k
      (splitCliffordHeadTailInfinityInvolute k
        (splitCliffordHeadTailOf k n x))
  rw [splitCliffordInfinityInvolute_ofStage,
    splitCliffordHeadTailInfinityInvolute_ofStage,
    splitCliffordHeadTailToInfinity_of]
  simp [splitCliffordHeadTailStageInvolute, splitCliffordInfinityOf]

end InfoGeometry.Canonical.SplitCliffordHeadTailTower

end
