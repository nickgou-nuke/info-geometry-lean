import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2BNPair

/-- Double coset of a subgroup B with a middle element g. -/
def doubleCoset {G : Type*} [Group G] (B : Subgroup G) (g : G) : Set G :=
  { x : G | ∃ b1 ∈ B, ∃ b2 ∈ B, x = b1 * g * b2 }

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
