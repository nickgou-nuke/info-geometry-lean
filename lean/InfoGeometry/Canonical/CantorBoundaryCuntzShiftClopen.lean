import InfoGeometry.Canonical.CantorBoundaryCuntzShiftTopology

/-!
# Clopen images of the symbolic Cuntz branches

The front-prefix maps have a particularly concrete topological image: the
image of `prefixBit b` is the cylinder fixing coordinate `0` to `b`.  This
module records that fact and derives the clopen property in the product
topology.  It does not introduce a new Cantor-space model or a new Cuntz
algebra; it is a topological consequence of the existing owner definitions.
-/

open Set TopologicalSpace

namespace InfoGeometry.Canonical.CantorBoundaryCuntzShift

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

theorem range_prefixBit_eq_coordinate_cylinder (b : Bool) :
    Set.range (prefixBit b) = (fun x : CantorBoundary => x 0) ⁻¹' ({b} : Set Bool) := by
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
    trivial
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

def prefixTail (y : CantorBoundary) : CantorBoundary :=
  fun n => y (n + 1)

theorem continuous_prefixTail : Continuous (prefixTail) := by
  apply continuous_pi
  intro n
  exact continuous_apply (n + 1)

noncomputable def prefixBitHomeomorphRange (b : Bool) :
    CantorBoundary ≃ₜ Set.range (prefixBit b) :=
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

theorem prefixBitHomeomorphRange_apply (b : Bool) (x : CantorBoundary) :
    prefixBitHomeomorphRange b x = ⟨prefixBit b x, ⟨x, rfl⟩⟩ :=
  rfl

end InfoGeometry.Canonical.CantorBoundaryCuntzShift
