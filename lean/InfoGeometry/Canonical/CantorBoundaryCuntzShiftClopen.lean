import InfoGeometry.Canonical.CantorBoundaryCuntzShiftTopology
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Clopen images of the symbolic Cuntz branches

The front-prefix maps have a particularly concrete topological image: the
image of `prefixBit b` is the cylinder fixing coordinate `0` to `b`.  This
module records that fact and derives the clopen property in the product
topology.  It does not introduce a new Cantor-space model or a new Cuntz
algebra; it is a topological consequence of the existing owner definitions.
-/

open Set TopologicalSpace
open CategoryTheory

namespace InfoGeometry.Canonical.CantorBoundaryCuntzShift

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology

theorem range_prefixBit_eq_coordinate_cylinder (b : Bool) :
    Set.range (prefixBit b) = (fun x : (ℕ → Bool) => x 0) ⁻¹' ({b} : Set Bool) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp [prefixBit]
  · intro hy
    have hy0 : y 0 = b := by
      simpa using hy
    refine ⟨fun n => y (n + 1), ?_⟩
    funext n
    cases n with
    | zero => exact hy0.symm
    | succ k => rfl

theorem isOpen_range_prefixBit (b : Bool) :
    IsOpen (Set.range (prefixBit b)) := by
  rw [range_prefixBit_eq_coordinate_cylinder b]
  exact (continuous_apply 0).isOpen_preimage _ (isOpen_discrete _)

theorem isClosed_range_prefixBit (b : Bool) :
    IsClosed (Set.range (prefixBit b)) := by
  rw [range_prefixBit_eq_coordinate_cylinder b]
  exact IsClosed.preimage (continuous_apply 0) (isClosed_discrete _)

theorem isClopen_range_prefixBit (b : Bool) :
    IsOpen (Set.range (prefixBit b)) ∧
      IsClosed (Set.range (prefixBit b)) :=
  ⟨isOpen_range_prefixBit b, isClosed_range_prefixBit b⟩

theorem isCompact_range_prefixBit (b : Bool) :
    IsCompact (Set.range (prefixBit b)) := by
  simpa [Set.range] using cantorBoundary_compact.image (continuous_prefixBit b)

theorem range_prefixBit_false_disjoint_true :
    Disjoint (Set.range (prefixBit false)) (Set.range (prefixBit true)) := by
  rw [range_prefixBit_eq_coordinate_cylinder false,
    range_prefixBit_eq_coordinate_cylinder true]
  refine Set.disjoint_left.2 ?_
  intro y hyFalse hyTrue
  have hFalse : y 0 = false := by simpa using hyFalse
  have hTrue : y 0 = true := by simpa using hyTrue
  rw [hFalse] at hTrue
  cases hTrue

theorem range_prefixBit_false_union_true :
    Set.range (prefixBit false) ∪ Set.range (prefixBit true) = Set.univ := by
  ext y
  constructor
  · intro
    exact Set.mem_univ y
  · intro
    cases hbit : y 0 with
    | false =>
        left
        refine ⟨fun n => y (n + 1), ?_⟩
        funext n
        cases n with
        | zero => exact hbit.symm
        | succ k => rfl
    | true =>
        right
        refine ⟨fun n => y (n + 1), ?_⟩
        funext n
        cases n with
        | zero => exact hbit.symm
        | succ k => rfl

theorem mem_range_prefixBit_iff (b : Bool) (y : (ℕ → Bool)) :
    y ∈ Set.range (prefixBit b) ↔ y 0 = b := by
  rw [range_prefixBit_eq_coordinate_cylinder b]
  rfl

theorem range_prefixBit_compl (b : Bool) :
    (Set.range (prefixBit b))ᶜ = Set.range (prefixBit (!b)) := by
  ext y
  rw [mem_compl_iff, mem_range_prefixBit_iff,
    mem_range_prefixBit_iff]
  cases b <;> cases h : y 0 <;> simp

theorem range_prefixBit_false_inter_true :
    Set.range (prefixBit false) ∩ Set.range (prefixBit true) = (∅ : Set (ℕ → Bool)) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyFalse, hyTrue⟩
    have hFalse : y 0 = false := (mem_range_prefixBit_iff false y).1 hyFalse
    have hTrue : y 0 = true := (mem_range_prefixBit_iff true y).1 hyTrue
    rw [hFalse] at hTrue
    cases hTrue
  · intro hy
    cases hy

def prefixTail (y : (ℕ → Bool)) : (ℕ → Bool) :=
  fun n => y (n + 1)

@[simp]
theorem prefixTail_prefixBit (b : Bool) (x : (ℕ → Bool)) :
    prefixTail (prefixBit b x) = x := by
  funext n
  rfl

theorem prefixBit_prefixTail_of_mem_range
    {b : Bool} {y : (ℕ → Bool)}
    (hy : y ∈ Set.range (prefixBit b)) :
    prefixBit b (prefixTail y) = y := by
  rcases hy with ⟨x, rfl⟩
  funext n
  cases n with
  | zero => rfl
  | succ k => rfl

theorem continuous_prefixTail : Continuous (prefixTail) := by
  apply continuous_pi
  intro n
  exact continuous_apply (n + 1)

noncomputable def prefixBitHomeomorphRange (b : Bool) :
    (ℕ → Bool) ≃ₜ Set.range (prefixBit b) :=
  { toEquiv :=
      { toFun := fun x => ⟨prefixBit b x, ⟨x, rfl⟩⟩
        invFun := fun y => prefixTail y.1
        left_inv := by
          intro x
          funext n
          rfl
        right_inv := by
          intro y
          rcases y.2 with ⟨x, hx⟩
          apply Subtype.ext
          funext n
          rw [← hx]
          cases n with
          | zero => rfl
          | succ k => exact (congrFun hx (k + 1)).symm }
    continuous_toFun := (continuous_prefixBit b).subtype_mk (fun x => ⟨x, rfl⟩)
    continuous_invFun := continuous_prefixTail.comp continuous_subtype_val }

theorem prefixBitHomeomorphRange_apply (b : Bool) (x : (ℕ → Bool)) :
    prefixBitHomeomorphRange b x = ⟨prefixBit b x, ⟨x, rfl⟩⟩ :=
  rfl

@[simp] theorem prefixBitHomeomorphRange_symm_apply
    (b : Bool) (y : Set.range (prefixBit b)) :
    (prefixBitHomeomorphRange b).symm y = prefixTail y.1 :=
  rfl

noncomputable def prefixBitRangeCompHausSource : CompHaus := by
  letI : CompactSpace (ℕ → Bool) := ⟨cantorBoundary_compact⟩
  exact CompHaus.of (ℕ → Bool)

noncomputable def prefixBitRangeCompHausTarget (b : Bool) : CompHaus := by
  letI : CompactSpace (ℕ → Bool) := ⟨cantorBoundary_compact⟩
  letI : CompactSpace (Set.range (prefixBit b)) :=
    isCompact_iff_compactSpace.mp (by
      simpa using cantorBoundary_compact.image (continuous_prefixBit b))
  exact CompHaus.of (Set.range (prefixBit b))

noncomputable def prefixBitRangeCompHausIso (b : Bool) :
    prefixBitRangeCompHausSource ≅ prefixBitRangeCompHausTarget b := by
  letI : CompactSpace (ℕ → Bool) := ⟨cantorBoundary_compact⟩
  letI : CompactSpace (Set.range (prefixBit b)) :=
    isCompact_iff_compactSpace.mp (by
      simpa using cantorBoundary_compact.image (continuous_prefixBit b))
  let e := prefixBitHomeomorphRange b
  letI : T2Space (Set.range (prefixBit b)) := e.t2Space
  change CompHaus.of (ℕ → Bool) ≅ CompHaus.of (Set.range (prefixBit b))
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        change e.symm (e x) = x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

theorem prefixBitRangeCompHausIso_hom_apply
    (b : Bool) (x : ℕ → Bool) :
    (prefixBitRangeCompHausIso b).hom x =
      prefixBitHomeomorphRange b x :=
  rfl

end InfoGeometry.Canonical.CantorBoundaryCuntzShift
