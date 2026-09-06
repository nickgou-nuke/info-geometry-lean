import InfoGeometry.Canonical.CantorBoundaryCuntzShiftClopen
import Mathlib.Topology.Category.TopCat.Basic

/-!
# `TopCat` packaging of the symbolic Cuntz branch cylinders

The Cantor prefix branch is already a native homeomorphism onto a clopen
cylinder.  This owner exposes that exact homeomorphism as a `TopCat` iso,
without introducing a second boundary model.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryCuntzShift

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

def prefixBitTopCatHom (b : Bool) :
    TopCat.of (ℕ → Bool) ⟶
      TopCat.of (Set.range (prefixBit b)) :=
  TopCat.ofHom
    { toFun := prefixBitHomeomorphRange b
      continuous_toFun := (prefixBitHomeomorphRange b).continuous }

def prefixBitTopCatInv (b : Bool) :
    TopCat.of (Set.range (prefixBit b)) ⟶ TopCat.of (ℕ → Bool) :=
  TopCat.ofHom
    { toFun := (prefixBitHomeomorphRange b).symm
      continuous_toFun := (prefixBitHomeomorphRange b).symm.continuous }

theorem prefixBitTopCatInv_comp_hom (b : Bool) :
    prefixBitTopCatHom b ≫ prefixBitTopCatInv b = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (prefixBitHomeomorphRange b).symm
      (prefixBitHomeomorphRange b x) = x
  exact (prefixBitHomeomorphRange b).left_inv x

theorem prefixBitTopCatHom_comp_inv (b : Bool) :
    prefixBitTopCatInv b ≫ prefixBitTopCatHom b = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change prefixBitHomeomorphRange b
      ((prefixBitHomeomorphRange b).symm x) = x
  exact (prefixBitHomeomorphRange b).right_inv x

def prefixBitTopCatIso (b : Bool) :
    TopCat.of (ℕ → Bool) ≅
      TopCat.of (Set.range (prefixBit b)) where
  hom := prefixBitTopCatHom b
  inv := prefixBitTopCatInv b
  hom_inv_id := prefixBitTopCatInv_comp_hom b
  inv_hom_id := prefixBitTopCatHom_comp_inv b

@[simp] theorem prefixBitTopCatHom_apply (b : Bool) (x : (ℕ → Bool)) :
    prefixBitTopCatHom b x =
      ⟨prefixBit b x, ⟨x, rfl⟩⟩ :=
  rfl

@[simp] theorem prefixBitTopCatInv_apply
    (b : Bool) (y : Set.range (prefixBit b)) :
    prefixBitTopCatInv b y = prefixTail y.1 :=
  rfl

theorem prefixBitTopCatIso_target_is_clopen (b : Bool) :
    IsOpen (Set.range (prefixBit b)) ∧
      IsClosed (Set.range (prefixBit b)) :=
  isClopen_range_prefixBit b

theorem prefixBitTopCat_targets_partition :
    Disjoint (Set.range (prefixBit false)) (Set.range (prefixBit true)) ∧
      Set.range (prefixBit false) ∪ Set.range (prefixBit true) = Set.univ := by
  constructor
  · refine Set.disjoint_left.2 ?_
    intro x hx hy
    rcases hx with ⟨u, hu⟩
    rcases hy with ⟨v, hv⟩
    have hhead := congrFun (hu.trans hv.symm) 0
    simp [prefixBit] at hhead
  · apply Set.eq_univ_of_forall
    intro x
    rcases prefixBit_range_cover x with hx | hx
    · exact Set.mem_union_left _ hx
    · exact Set.mem_union_right _ hx

end InfoGeometry.Canonical.CantorBoundaryCuntzShift
