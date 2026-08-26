import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2BNPair

/-- Double coset of a subgroup B with a middle element g. -/
def doubleCoset {G : Type*} [Group G] (B : Subgroup G) (g : G) : Set G :=
  { x : G | ∃ b1 ∈ B, ∃ b2 ∈ B, x = b1 * g * b2 }

/-- Membership in a double coset is equivalent to reaching the corresponding
left quotient class by left translation from the Borel subgroup.  This is the
quotient/orbit interface used to transport a finite flag-orbit certificate
into a group-level Bruhat cover. -/
theorem mem_doubleCoset_iff_quotient_smul
    {G : Type*} [Group G] (B : Subgroup G) (w g : G) :
    g ∈ doubleCoset B w ↔ ∃ b : G, b ∈ B ∧
      b • (QuotientGroup.mk w : G ⧸ B) = QuotientGroup.mk g := by
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    refine ⟨b₁, hb₁, ?_⟩
    change (QuotientGroup.mk (b₁ * w) : G ⧸ B) = QuotientGroup.mk (b₁ * w * b₂)
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hb₂
  · rintro ⟨b, hb, hq⟩
    change (QuotientGroup.mk (b * w) : G ⧸ B) = QuotientGroup.mk g at hq
    rw [QuotientGroup.eq] at hq
    change (b * w)⁻¹ * g ∈ B at hq
    refine ⟨b, hb, (b * w)⁻¹ * g, hq, ?_⟩
    simp [mul_assoc]

/-! A quotient-orbit separation theorem transports directly to double-coset
disjointness.  This is the interface used by concrete finite Bruhat owners:
the finite separation argument belongs on `G ⧸ B`, while this lemma performs
only the structural transport back to `G`. -/

def quotientOrbit {G : Type*} [Group G] (B : Subgroup G) (w : G) : Set (G ⧸ B) :=
  {q | ∃ b : G, b ∈ B ∧
    b • (QuotientGroup.mk w : G ⧸ B) = q}

theorem disjoint_doubleCoset_of_disjoint_quotientOrbit
    {G : Type*} [Group G] (B : Subgroup G) (w₁ w₂ : G)
    (h : Disjoint (quotientOrbit B w₁) (quotientOrbit B w₂)) :
    Disjoint (doubleCoset B w₁) (doubleCoset B w₂) := by
  rw [Set.disjoint_left]
  intro g hg₁ hg₂
  have hq₁ : QuotientGroup.mk g ∈ quotientOrbit B w₁ := by
    exact (mem_doubleCoset_iff_quotient_smul B w₁ g).mp hg₁
  have hq₂ : QuotientGroup.mk g ∈ quotientOrbit B w₂ := by
    exact (mem_doubleCoset_iff_quotient_smul B w₂ g).mp hg₂
  exact (Set.disjoint_left.mp h) hq₁ hq₂

/-! The converse transport is useful when a concrete double-coset
separation certificate is obtained from finite PC coordinates. -/

theorem disjoint_quotientOrbit_of_disjoint_doubleCoset
    {G : Type*} [Group G] (B : Subgroup G) (w₁ w₂ : G)
    (h : Disjoint (doubleCoset B w₁) (doubleCoset B w₂)) :
    Disjoint (quotientOrbit B w₁) (quotientOrbit B w₂) := by
  rw [Set.disjoint_left]
  intro q hq₁ hq₂
  rcases hq₁ with ⟨b₁, hb₁, hq₁⟩
  rcases hq₂ with ⟨b₂, hb₂, hq₂⟩
  have hg₁ : b₁ * w₁ ∈ doubleCoset B w₁ := by
    apply (mem_doubleCoset_iff_quotient_smul B w₁ (b₁ * w₁)).2
    refine ⟨b₁, hb₁, ?_⟩
    change (QuotientGroup.mk (b₁ * w₁) : G ⧸ B) =
      b₁ • (QuotientGroup.mk w₁ : G ⧸ B)
    rfl
  have hg₂ : b₁ * w₁ ∈ doubleCoset B w₂ := by
    apply (mem_doubleCoset_iff_quotient_smul B w₂ (b₁ * w₁)).2
    refine ⟨b₂, hb₂, ?_⟩
    change b₂ • (QuotientGroup.mk w₂ : G ⧸ B) =
      (QuotientGroup.mk (b₁ * w₁) : G ⧸ B)
    exact hq₂.trans hq₁.symm
  exact (Set.disjoint_left.mp h) hg₁ hg₂

/-! A double-coset cover is already a generation theorem once the middle
representatives and the Borel subgroup are included among the generators. -/

theorem closure_eq_top_of_doubleCoset_cover
    {G : Type*} [Group G] (B : Subgroup G) (R : Set G)
    (hcover : ∀ g : G, ∃ w ∈ R, g ∈ doubleCoset B w) :
    Subgroup.closure ((B : Set G) ∪ R) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨w, hw, b₁, hb₁, b₂, hb₂, rfl⟩ := hcover g
  have hb₁' : b₁ ∈ Subgroup.closure ((B : Set G) ∪ R) :=
    Subgroup.subset_closure (Or.inl hb₁)
  have hw' : w ∈ Subgroup.closure ((B : Set G) ∪ R) :=
    Subgroup.subset_closure (Or.inr hw)
  have hb₂' : b₂ ∈ Subgroup.closure ((B : Set G) ∪ R) :=
    Subgroup.subset_closure (Or.inl hb₂)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb₁' hw') hb₂'

/-- Structure defining a Tits system / (B, N) pair on a group G. -/
structure TitsSystem (G : Type*) [Group G] where
  B : Subgroup G
  N : Subgroup G
  W : Type*
  fintypeW : Fintype W
  groupW : Group W
  toW : N →* W
  toW_ker : ∀ (n : N), toW n = 1 ↔ (n : G) ∈ B
  S : Set W
  S_involutive : ∀ s ∈ S, s * s = 1
  -- Bruhat cell disjointness theorem:
  cell_disjoint : ∀ (w1 w2 : N), toW w1 ≠ toW w2 →
    Disjoint (doubleCoset B (w1 : G)) (doubleCoset B (w2 : G))
  -- Bruhat cell covering:
  cell_cover : ∀ g : G, ∃ w : N, g ∈ doubleCoset B (w : G)

attribute [instance] TitsSystem.fintypeW TitsSystem.groupW

namespace TitsSystem

variable {G : Type*} [Group G] (ts : TitsSystem G)

/-! A finite Bruhat partition packages only the extra data needed to turn the
abstract cell-cover axioms into a cardinality identity.  In particular, this
does not manufacture a BN-pair for any concrete carrier. -/

structure FiniteBruhatPartition (ts : TitsSystem G) where
  representative : ts.W → ts.N
  representative_toW : ∀ w, ts.toW (representative w) = w
  cover : ∀ g : G, ∃ w : ts.W,
    g ∈ doubleCoset ts.B (representative w : G)

namespace FiniteBruhatPartition

variable (bp : FiniteBruhatPartition ts)

def cell (w : ts.W) : Set G :=
  doubleCoset ts.B (bp.representative w : G)

theorem cell_disjoint {w₁ w₂ : ts.W} (h : w₁ ≠ w₂) :
    Disjoint (cell ts bp w₁) (cell ts bp w₂) := by
  apply ts.cell_disjoint
  simpa [bp.representative_toW] using h

noncomputable def chooseCell (g : G) : ts.W :=
  Classical.choose (FiniteBruhatPartition.cover bp g)

theorem chooseCell_mem (g : G) :
    g ∈ cell ts bp (chooseCell ts bp g) := by
  exact Classical.choose_spec (FiniteBruhatPartition.cover bp g)

noncomputable def cellEquiv :
    G ≃ Σ w : ts.W, {g : G // g ∈ cell ts bp w} where
  toFun g := ⟨chooseCell ts bp g, ⟨g, chooseCell_mem ts bp g⟩⟩
  invFun z := z.2.1
  left_inv g := by
    rfl
  right_inv z := by
    rcases z with ⟨w, g, hg⟩
    dsimp
    have hindex : chooseCell ts bp g = w := by
      by_contra hne
      have h₁ : g ∈ cell ts bp (chooseCell ts bp g) :=
        chooseCell_mem ts bp g
      have h₂ : g ∈ cell ts bp w := hg
      exact (Set.disjoint_left.1 (cell_disjoint ts bp hne) h₁) h₂
    subst hindex
    rfl

noncomputable instance cellFintype [Fintype G] (bp : FiniteBruhatPartition ts)
    (w : ts.W) : Fintype {g : G // g ∈ cell ts bp w} :=
  letI : Finite {g : G // g ∈ cell ts bp w} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  Fintype.ofFinite _

theorem card_eq_sum_cell_cards (bp : FiniteBruhatPartition ts) [Fintype G] :
    Fintype.card G =
      ∑ w : ts.W, Fintype.card {g : G // g ∈ cell ts bp w} := by
  rw [Fintype.card_congr (cellEquiv ts bp), Fintype.card_sigma]

end FiniteBruhatPartition

/-- Double coset contains its base representative. -/
theorem self_mem_doubleCoset (g : G) :
    g ∈ doubleCoset ts.B g :=
  ⟨1, ts.B.one_mem, 1, ts.B.one_mem, by rw [mul_one, one_mul]⟩

/-- Shift by left multiplication from B stays in the double coset. -/
theorem left_mul_mem_doubleCoset (b : G) (hb : b ∈ ts.B) (g : G) :
    b * g ∈ doubleCoset ts.B g :=
  ⟨b, hb, 1, ts.B.one_mem, by rw [mul_one]⟩

/-- 🏆 THEOREM: Double cosets of elements differing by torus B ∩ N are identical. -/
theorem doubleCoset_eq_of_toW_eq (w1 w2 : ts.N) (h : ts.toW w1 = ts.toW w2) :
    doubleCoset ts.B (w1 : G) = doubleCoset ts.B (w2 : G) := by
  have h_diff : ts.toW (w1 * w2⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h_in_B : ((w1 * w2⁻¹ : ts.N) : G) ∈ ts.B :=
    (ts.toW_ker (w1 * w2⁻¹)).mp h_diff
  ext x
  constructor
  · rintro ⟨b1, hb1, b2, hb2, rfl⟩
    have hw1 : (w1 : G) = ((w1 * w2⁻¹ : ts.N) : G) * (w2 : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [hw1]
    use b1 * ((w1 * w2⁻¹ : ts.N) : G)
    refine ⟨ts.B.mul_mem hb1 h_in_B, b2, hb2, ?_⟩
    group
  · rintro ⟨b1, hb1, b2, hb2, rfl⟩
    have h_diff2 : ts.toW (w2 * w1⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have h_in_B2 : ((w2 * w1⁻¹ : ts.N) : G) ∈ ts.B :=
      (ts.toW_ker (w2 * w1⁻¹)).mp h_diff2
    have hw2 : (w2 : G) = ((w2 * w1⁻¹ : ts.N) : G) * (w1 : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
    rw [hw2]
    use b1 * ((w2 * w1⁻¹ : ts.N) : G)
    refine ⟨ts.B.mul_mem hb1 h_in_B2, b2, hb2, ?_⟩
    group

/-- 🏆 MASTER THEOREM: Two Bruhat cells are equal IF AND ONLY IF their Weyl images coincide. -/
theorem doubleCoset_eq_iff (w1 w2 : ts.N) :
    doubleCoset ts.B (w1 : G) = doubleCoset ts.B (w2 : G) ↔ ts.toW w1 = ts.toW w2 := by
  constructor
  · intro h
    by_contra hne
    have hdisj := ts.cell_disjoint w1 w2 hne
    have hx : (w1 : G) ∈ doubleCoset ts.B (w1 : G) := ts.self_mem_doubleCoset (w1 : G)
    have hx2 : (w1 : G) ∈ doubleCoset ts.B (w2 : G) := by rw [← h]; exact hx
    exact Set.disjoint_iff.mp hdisj ⟨hx, hx2⟩
  · exact ts.doubleCoset_eq_of_toW_eq w1 w2

/-- 🏆 THEOREM: Uniqueness of Bruhat Weyl cell representative for any group element. -/
theorem unique_bruhat_cell_weyl (g : G) :
    ∃! w : ts.W, ∃ (n : ts.N), ts.toW n = w ∧ g ∈ doubleCoset ts.B (n : G) := by
  rcases ts.cell_cover g with ⟨n, hn⟩
  use ts.toW n
  refine ⟨⟨n, rfl, hn⟩, ?_⟩
  rintro w ⟨n', rfl, hn'⟩
  by_contra hne
  have hdisj := ts.cell_disjoint n' n hne
  exact Set.disjoint_iff.mp hdisj ⟨hn', hn⟩

end TitsSystem

end InfoGeometry.Algebra.Zorn.G2BNPair

end noncomputable section
