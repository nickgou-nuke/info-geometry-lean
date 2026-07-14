import InfoGeometry.Algebra

namespace InfoGeometry.Algebra.CuntzRecursiveFermionSystem

/-!
# Maya Diagrams and the Infinite Wedge Representation

Following Katsunori Kawamura, "Extensions of representations of the CAR algebra
to the Cuntz algebra O₂".

We construct the branching functions on the space of Maya diagrams which give
rise to the infinite wedge representation of the CAR algebra and its standard
extension to the Cuntz algebra O₂.
-/

/-- The half-integer lattice Z + 1/2 is mapped to ℤ via `k = j - 1/2`.
    Positive half-integers map to `j ≥ 1`. Negative half-integers map to `j ≤ 0`. -/
abbrev MayaIndex := ℤ

/-- The vacuum state Z₋ = { -1/2, -3/2, ... } corresponding to j ≤ 0. -/
def vacuum : Set MayaIndex := Set.Iic 0

/-- The dual vacuum state Z₊ = { 1/2, 3/2, ... } corresponding to j ≥ 1. -/
def dual_vacuum : Set MayaIndex := Set.Ici 1

/-- A Maya diagram is a subset whose symmetric difference with the vacuum is finite. -/
def IsMaya (S : Set MayaIndex) : Prop :=
  (symmDiff S vacuum).Finite

/-- A Dual Maya diagram is a subset whose symmetric difference with the dual vacuum is finite. -/
def IsDualMaya (S : Set MayaIndex) : Prop :=
  (symmDiff S dual_vacuum).Finite

structure MayaDiagram where
  S : Set MayaIndex
  is_maya : IsMaya S

structure DualMayaDiagram where
  S : Set MayaIndex
  is_dual_maya : IsDualMaya S

/-! ## Branching Functions on Maya Diagrams -/

/-- The S_+ component (positive half-integers). -/
def S_plus (S : Set MayaIndex) : Set MayaIndex :=
  S ∩ Set.Ici 1

/-- The S_- component (negative half-integers). -/
def S_minus (S : Set MayaIndex) : Set MayaIndex :=
  S ∩ Set.Iic 0

/-- The index shift +1, corresponding to `k + 1` on the half-integer lattice. -/
def shift_plus (S : Set MayaIndex) : Set MayaIndex :=
  { j | ∃ i ∈ S, j = i + 1 }

/-- The index negation, corresponding to `-k` on the half-integer lattice.
    Since `k = j - 1/2`, `-k = -j + 1/2 = (1 - j) - 1/2`. -/
def negate_index (S : Set MayaIndex) : Set MayaIndex :=
  { j | ∃ i ∈ S, j = 1 - i }

/-- The branching function g₁ : S ↦ -(S_{+, +1} ∪ S_- ∪ {1/2}) -/
def g1 (S : Set MayaIndex) : Set MayaIndex :=
  negate_index (shift_plus (S_plus S) ∪ (S_minus S) ∪ {1})

/-- The branching function g₂ : S ↦ -(S_{+, +1} ∪ S_-) -/
def g2 (S : Set MayaIndex) : Set MayaIndex :=
  negate_index (shift_plus (S_plus S) ∪ (S_minus S))

/-! ## Finiteness Helper Lemmas -/

/-- The "particles" (elements ≥ 1 in S) are finite for a Maya diagram. -/
theorem maya_particles_finite {S : Set MayaIndex} (hS : IsMaya S) :
    (S ∩ Set.Ici 1).Finite := by
  apply Set.Finite.subset hS
  rw [Set.symmDiff_def]
  rintro x ⟨hxS, hx1⟩
  simp only [Set.mem_union, Set.mem_diff]
  left
  refine ⟨hxS, ?_⟩
  intro h_vac
  have h_vac' : x ≤ 0 := h_vac
  have h_1 : 1 ≤ x := hx1
  linarith

/-- The "holes" (elements ≤ 0 not in S) are finite for a Maya diagram. -/
theorem maya_holes_finite {S : Set MayaIndex} (hS : IsMaya S) :
    (Set.Iic 0 \ S).Finite := by
  apply Set.Finite.subset hS
  rw [Set.symmDiff_def]
  rintro x ⟨hx0, hxS⟩
  simp only [Set.mem_union, Set.mem_diff]
  right
  exact ⟨hx0, hxS⟩

theorem shift_plus_finite {A : Set MayaIndex} (hA : A.Finite) :
    (shift_plus A).Finite := by
  apply Set.Finite.subset (hA.image (· + 1))
  rintro j ⟨i, hi, rfl⟩
  exact Set.mem_image_of_mem _ hi

theorem negate_index_finite {A : Set MayaIndex} (hA : A.Finite) :
    (negate_index A).Finite := by
  apply Set.Finite.subset (hA.image (1 - ·))
  rintro j ⟨i, hi, rfl⟩
  exact Set.mem_image_of_mem _ hi

/-- The S_plus component is finite for Maya diagrams. -/
theorem S_plus_finite {S : Set MayaIndex} (hS : IsMaya S) :
    (S_plus S).Finite :=
  maya_particles_finite hS

/-! ## Main Colimit Lemma: g₂ maps Maya diagrams to Dual Maya diagrams -/

/-- Membership characterization for `negate_index` applied to a union. -/
private theorem mem_negate_index_union (A B : Set MayaIndex) (j : MayaIndex) :
    j ∈ negate_index (A ∪ B) ↔ j ∈ negate_index A ∨ j ∈ negate_index B := by
  simp only [negate_index, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨i, hi | hi, rfl⟩
    · left; exact ⟨i, hi, rfl⟩
    · right; exact ⟨i, hi, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, Or.inl hi, rfl⟩
    · exact ⟨i, Or.inr hi, rfl⟩

/-- g₂ maps Maya diagrams (M₊) to Dual Maya diagrams (M₋).
    This is the core colimit property of Kawamura's branching functions. -/
theorem g2_maps_maya_to_dual_maya {S : Set MayaIndex} (hS : IsMaya S) :
    IsDualMaya (g2 S) := by
  unfold IsDualMaya g2
  rw [Set.symmDiff_def]
  apply Set.Finite.subset ((negate_index_finite (shift_plus_finite (S_plus_finite hS))).union
    (negate_index_finite (maya_holes_finite hS)))
  intro j hj
  simp only [Set.mem_union, Set.mem_diff] at hj ⊢
  rcases hj with ⟨hjg, hjdv⟩ | ⟨hjdv, hjg⟩
  · -- j ∈ negate_index(shift_plus(S_plus S) ∪ S_minus S) but j ∉ dual_vacuum
    have hj_lt_1 : ¬(1 ≤ j) := hjdv
    -- Decompose using negate_index distribution over union
    rw [mem_negate_index_union] at hjg
    rcases hjg with hjL | hjR
    · -- j came from negate_index(shift_plus(S_plus S)), which is finite
      left; exact hjL
    · -- j came from negate_index(S_minus S): impossible since j < 1
      exfalso
      obtain ⟨i, hi_mem, hjEq⟩ := hjR
      have hi0 : i ≤ 0 := hi_mem.2
      linarith
  · -- j ∈ dual_vacuum but j ∉ negate_index(...)
    have hj_ge_1 : 1 ≤ j := hjdv
    -- (1-j) is a hole: (1-j) ≤ 0 and (1-j) ∉ S
    right
    refine ⟨1 - j, ?_, by ring⟩
    simp only [Set.mem_diff, Set.mem_Iic]
    refine ⟨?_, ?_⟩
    · -- 1 - j ≤ 0
      linarith
    · intro hjS
      apply hjg
      rw [mem_negate_index_union]
      right
      refine ⟨1 - j, ⟨hjS, ?_⟩, by ring⟩
      show 1 - j ≤ 0
      linarith

/-- g₁ maps Maya diagrams (M₊) to Dual Maya diagrams (M₋).
    g₁ differs from g₂ only by inserting {1} before negate_index,
    which adds the single element 0 to g1(S). -/
theorem g1_maps_maya_to_dual_maya {S : Set MayaIndex} (hS : IsMaya S) :
    IsDualMaya (g1 S) := by
  unfold IsDualMaya g1
  rw [Set.symmDiff_def]
  -- Bounding set: negate_index(shift_plus(S_plus S)) ∪ {0} ∪ negate_index(holes)
  apply Set.Finite.subset ((negate_index_finite (shift_plus_finite (S_plus_finite hS))).union
    ((Set.finite_singleton (0 : MayaIndex)).union
    (negate_index_finite (maya_holes_finite hS))))
  intro j hj
  simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hj ⊢
  rcases hj with ⟨hjg1, hjdv⟩ | ⟨hjdv, hjg1⟩
  · -- j ∈ g1 S but j ∉ dual_vacuum
    have hj_lt_1 : ¬(1 ≤ j) := hjdv
    -- Decompose: negate_index distributes over the triple union
    rw [mem_negate_index_union] at hjg1
    rcases hjg1 with hjA | hj1
    · -- j came from negate_index(shift_plus(S_plus S) ∪ S_minus S)
      rw [mem_negate_index_union] at hjA
      rcases hjA with hjL | hjR
      · left; exact hjL
      · exfalso
        obtain ⟨i, hi_mem, hjEq⟩ := hjR
        have hi0 : i ≤ 0 := hi_mem.2
        linarith
    · -- j came from negate_index({1}) = {0}
      right; left
      obtain ⟨i, hi, rfl⟩ := hj1
      have hi1 : i = 1 := hi
      show 1 - i = 0
      linarith
  · -- j ∈ dual_vacuum but j ∉ g1 S
    have hj_ge_1 : 1 ≤ j := hjdv
    right; right
    refine ⟨1 - j, ?_, by ring⟩
    simp only [Set.mem_diff, Set.mem_Iic]
    refine ⟨?_, ?_⟩
    · linarith
    · intro hjS
      apply hjg1
      rw [mem_negate_index_union]
      left
      rw [mem_negate_index_union]
      right
      refine ⟨1 - j, ⟨hjS, ?_⟩, by ring⟩
      show 1 - j ≤ 0
      linarith

/-! ## Wedge Actions (sorry-free) -/

/-- Under the Cuntz infinite wedge representation, s₁ acts on Maya diagrams via g₁,
    and s₂ acts via g₂. -/
def wedge_action_s1 (S : MayaDiagram) : DualMayaDiagram :=
  ⟨g1 S.S, g1_maps_maya_to_dual_maya S.is_maya⟩

def wedge_action_s2 (S : MayaDiagram) : DualMayaDiagram :=
  ⟨g2 S.S, g2_maps_maya_to_dual_maya S.is_maya⟩

/-! ## Connection to the Recursive Fermion System -/

open InfoGeometry.Topology InfoGeometry.Algebra in
/-- The recursive fermion generators from KawamuraCuntzCAR.
    aₙ = ζ^{n-1}(s₁ s₂*) -/
noncomputable def RFS_fermion {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (n : ℕ) : Op :=
  kawamuraCARSequence C n

end InfoGeometry.Algebra.CuntzRecursiveFermionSystem
