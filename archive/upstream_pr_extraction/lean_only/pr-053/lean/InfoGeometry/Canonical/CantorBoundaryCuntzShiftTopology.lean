import Mathlib.Topology.Constructions
import InfoGeometry.Canonical.CantorBoundaryCuntzShift
import InfoGeometry.Canonical.CantorBoundaryFiniteReadout

/-!
# Product-topology facts for the two symbolic Cuntz branches

The front-prefix maps are the finite-cylinder maps underlying the two symbolic
branches.  This owner records only their native topological and readout facts:
continuity, injectivity, disjoint branch images, and the affine recursion of
the binary readout.
-/

noncomputable section

open scoped Topology BigOperators

namespace InfoGeometry.Canonical.CantorBoundaryCuntzShift

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout

theorem continuous_prefixBit_topology (b : Bool) :
    Continuous (prefixBit b) := by
  apply continuous_pi
  intro n
  cases n with
  | zero => exact continuous_const
  | succ n => exact continuous_apply n

theorem continuous_boundaryHead :
    Continuous (boundaryHead : (ℕ → Bool) → Bool) := by
  exact continuous_apply 0

theorem continuous_boundaryTail :
    Continuous (boundaryTail : (ℕ → Bool) → (ℕ → Bool)) := by
  apply continuous_pi
  intro n
  exact continuous_apply (n + 1)

theorem boundaryTail_prefixBit (b : Bool) (x : (ℕ → Bool)) :
    boundaryTail (prefixBit b x) = x := by
  funext n
  rfl

theorem prefixBit_boundaryTail_of_head
    (b : Bool) (x : (ℕ → Bool))
    (h : boundaryHead x = b) :
    prefixBit b (boundaryTail x) = x := by
  funext n
  cases n with
  | zero => simpa [boundaryHead] using h.symm
  | succ n => rfl

theorem injective_prefixBit (b : Bool) :
    Function.Injective (prefixBit b) := by
  intro x y h
  funext n
  exact congrFun h (n + 1)

theorem left_right_branch_images_disjoint
    (x y : (ℕ → Bool)) :
    prefixBit false x ≠ prefixBit true y := by
  intro h
  have hzero := congrFun h 0
  simp [prefixBit] at hzero

theorem prefixBit_head_tail_topology (x : (ℕ → Bool)) :
    prefixBit (boundaryHead x) (boundaryTail x) = x := by
  simpa [prefixBit] using (boundary_recursive_decomposition x).symm

theorem prefixBit_range_cover_topology (x : (ℕ → Bool)) :
    (∃ y, prefixBit false y = x) ∨ ∃ y, prefixBit true y = x := by
  cases h : boundaryHead x with
  | false =>
      left
      exact ⟨boundaryTail x, by simpa [h] using prefixBit_head_tail_topology x⟩
  | true =>
      right
      exact ⟨boundaryTail x, by simpa [h] using prefixBit_head_tail_topology x⟩

theorem prefixBit_range_eq_head_preimage (b : Bool) :
    Set.range (prefixBit b) = boundaryHead ⁻¹' ({b} : Set Bool) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [boundaryHead, prefixBit]
  · intro hx
    have hhead : boundaryHead x = b := by
      simpa only [Set.mem_singleton_iff] using hx
    refine ⟨boundaryTail x, ?_⟩
    funext n
    cases n with
    | zero => exact hhead.symm
    | succ n => rfl

theorem isClosed_prefixBit_range_topology (b : Bool) :
    IsClosed (Set.range (prefixBit b)) := by
  rw [prefixBit_range_eq_head_preimage]
  exact isClosed_singleton.preimage continuous_boundaryHead

theorem isOpen_prefixBit_range_topology (b : Bool) :
    IsOpen (Set.range (prefixBit b)) := by
  rw [prefixBit_range_eq_head_preimage]
  exact continuous_boundaryHead.isOpen_preimage ({b} : Set Bool)
    (isOpen_discrete ({b} : Set Bool))

theorem isClopen_prefixBit_range_topology (b : Bool) :
    IsClopen (Set.range (prefixBit b)) := by
  exact ⟨isClosed_prefixBit_range_topology b, isOpen_prefixBit_range_topology b⟩

theorem isClosed_appendBitAtDepth_range (n : ℕ) (b : Bool) :
    IsClosed (Set.range (appendBitAtDepth n b)) := by
  rw [appendBitAtDepth_range_eq]
  exact isClosed_singleton.preimage (continuous_apply n)

theorem isOpen_appendBitAtDepth_range (n : ℕ) (b : Bool) :
    IsOpen (Set.range (appendBitAtDepth n b)) := by
  rw [appendBitAtDepth_range_eq]
  have hc : Continuous (fun x : (ℕ → Bool) => x n) := continuous_apply n
  exact hc.isOpen_preimage ({b} : Set Bool)
    (isOpen_discrete ({b} : Set Bool))

theorem isClopen_appendBitAtDepth_range (n : ℕ) (b : Bool) :
    IsClopen (Set.range (appendBitAtDepth n b)) := by
  exact ⟨isClosed_appendBitAtDepth_range n b,
    isOpen_appendBitAtDepth_range n b⟩

theorem appendBitAtDepth_range_inter (n : ℕ) :
    Set.range (appendBitAtDepth n false) ∩
        Set.range (appendBitAtDepth n true) = ∅ := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := hx.1
    obtain ⟨v, hv⟩ := hx.2
    exact False.elim
      (appendBitAtDepth_left_right_disjoint n u v (hu.trans hv.symm))
  · intro hx
    exact hx.elim

theorem appendBitAtDepth_false_range_compl (n : ℕ) :
    (Set.range (appendBitAtDepth n false))ᶜ =
      Set.range (appendBitAtDepth n true) := by
  rw [appendBitAtDepth_range_eq, appendBitAtDepth_range_eq]
  ext x
  cases h : x n <;> simp [h]

theorem prefixBit_range_union_topology :
    Set.range (prefixBit false) ∪ Set.range (prefixBit true) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact prefixBit_range_cover_topology x

theorem prefixBit_range_inter :
    Set.range (prefixBit false) ∩ Set.range (prefixBit true) = ∅ := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx.1
    obtain ⟨z, hz⟩ := hx.2
    exact False.elim (left_right_branch_images_disjoint y z (hy.trans hz.symm))
  · intro hx
    exact hx.elim

theorem prefixBit_false_range_compl :
    (Set.range (prefixBit false))ᶜ = Set.range (prefixBit true) := by
  ext x
  constructor
  · intro hx
    rcases prefixBit_range_cover_topology x with hfalse | htrue
    · exact False.elim (hx hfalse)
    · exact htrue
  · intro htrue hfalse
    rcases htrue with ⟨y, hy⟩
    rcases hfalse with ⟨z, hz⟩
    exact left_right_branch_images_disjoint z y (hz.trans hy.symm)

theorem realBinaryReadout_prefixBit
    (b : Bool) (x : (ℕ → Bool)) :
    realBinaryReadout (prefixBit b x) =
      (if b then (1 / 2 : ℝ) else 0) +
        (1 / 2 : ℝ) * realBinaryReadout x := by
  exact realBinaryReadout_boundaryCons b x

theorem realBinaryReadout_leftShift
    (x : (ℕ → Bool)) :
    realBinaryReadout (leftShift x) =
      (1 / 2 : ℝ) * realBinaryReadout x := by
  simpa [leftShift] using realBinaryReadout_prefixBit false x

theorem realBinaryReadout_rightShift
    (x : (ℕ → Bool)) :
    realBinaryReadout (rightShift x) =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * realBinaryReadout x := by
  simpa [rightShift] using realBinaryReadout_prefixBit true x

end InfoGeometry.Canonical.CantorBoundaryCuntzShift
