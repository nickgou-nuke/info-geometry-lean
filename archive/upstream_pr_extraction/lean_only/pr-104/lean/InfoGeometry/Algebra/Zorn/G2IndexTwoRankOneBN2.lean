import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Basic

/-!
# Rank-One Levi Split via Subgroup Index 2 and Involution Conjugation in Lean 4

Formalizes the pure group-theoretic proof of the (BN2) axiom:
  `s B s ⊆ B ∪ B s B`
for any group `G`, subgroup `B ≤ G`, and involution `s ∈ G` (`s² = 1`),
given an index-2 sub-Borel subgroup `H ≤ B` such that:
  1. `H` is stable under `s`-conjugation: `s H s ⊆ B`.
  2. The odd coset generator `r ∈ B \ H` satisfies the rank-1 Levi relation:
       `s * r * s = r * s * r`.
  3. `B` partitions as the 2-coset union `B = H ∪ r H`.

This eliminates 64-element matrix polynomial verifications in favor of a
2-coset structural split.
-/

variable {G : Type*} [Group G]

namespace InfoGeometry.Algebra.Zorn.IndexTwoLevi

/-! =========================================================================
    1. Bruhat Double-Coset Cell Definitions
    ========================================================================= -/

/-- Predicate for membership in the big Bruhat double coset `B s B`. -/
def InCellBsB (B : Subgroup G) (s x : G) : Prop :=
  ∃ b₁ ∈ B, ∃ b₂ ∈ B, x = b₁ * s * b₂

/-- Predicate for membership in the Bruhat cover `B ∪ B s B`. -/
def InBruhatCover (B : Subgroup G) (s x : G) : Prop :=
  x ∈ B ∨ InCellBsB B s x

/-! =========================================================================
    2. Index-2 Rank-1 Levi Split Theorem
    ========================================================================= -/

/--
MAIN THEOREM (Index-2 Rank-1 Levi Split):
If `H ≤ B` is an index-2 subgroup invariant under `s`-conjugation (`s H s ⊆ B`),
and the coset generator `r ∈ B` satisfies the Levi identity `s * r * s = r * s * r`,
then every element of `B = H ∪ r H` satisfies `s * b * s ∈ B ∪ B s B`.
-/
theorem bn2_of_index2_split (B : Subgroup G) (H : Subgroup G)
    (s : G) (hs : s * s = 1)
    (r : G) (hrB : r ∈ B)
    (h_H_conj : ∀ h ∈ H, s * h * s ∈ B)
    (h_levi : s * r * s = r * s * r)
    (b : G) (hb : b ∈ B)
    (h_split : b ∈ H ∨ ∃ h ∈ H, b = r * h) :
    InBruhatCover B s (s * b * s) := by
  rcases h_split with hbH | ⟨h, hhH, rfl⟩
  · -- Case 1: b ∈ H (Even / Toral branch)
    left
    exact h_H_conj b hbH
  · -- Case 2: b = r * h with h ∈ H (Odd / Big-Cell branch)
    right
    have h_conj_split : s * (r * h) * s = (s * r * s) * (s * h * s) := by
      calc
        s * (r * h) * s = s * r * (h * s) := by simp only [mul_assoc]
        _ = s * r * (1 * (h * s)) := by rw [one_mul]
        _ = s * r * ((s * s) * (h * s)) := by rw [hs]
        _ = (s * r * s) * (s * h * s) := by simp only [mul_assoc]
    rw [h_conj_split, h_levi]
    have h_shs : s * h * s ∈ B := h_H_conj h hhH
    have h_right : r * (s * h * s) ∈ B := B.mul_mem hrB h_shs
    refine ⟨r, hrB, r * (s * h * s), h_right, ?_⟩
    simp only [mul_assoc]

/--
COROLLARY (Global Set Inclusion from Index-2 Partition):
If every element `b ∈ B` decomposes into `H ∪ r H`, then `s B s ⊆ B ∪ B s B`.
-/
theorem bn2_set_inclusion_of_index2_split (B : Subgroup G) (H : Subgroup G)
    (s : G) (hs : s * s = 1)
    (r : G) (hrB : r ∈ B)
    (h_H_conj : ∀ h ∈ H, s * h * s ∈ B)
    (h_levi : s * r * s = r * s * r)
    (h_cover : ∀ b ∈ B, b ∈ H ∨ ∃ h ∈ H, b = r * h) :
    ∀ x ∈ { y | ∃ b ∈ B, y = s * b * s }, InBruhatCover B s x := by
  rintro x ⟨b, hb, rfl⟩
  exact bn2_of_index2_split B H s hs r hrB h_H_conj h_levi b hb (h_cover b hb)

end InfoGeometry.Algebra.Zorn.IndexTwoLevi
