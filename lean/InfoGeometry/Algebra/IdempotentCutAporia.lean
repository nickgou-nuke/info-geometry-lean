/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

/-!
# Four-corner identities for an idempotent cut

For an idempotent `p` and an idempotent `ω` in an associative ring, this
module records the four Peirce corners of `ω` relative to `p` and `1 - p`.
It proves the exact corner formulas, including the diagonal idempotency
defects.  The carrier remains an arbitrary associative ring: these lemmas do
not assert that a split-octonion or other nonassociative product is associative.
-/

namespace InfoGeometry.Algebra.IdempotentCutAporia

variable {A : Type*} [Ring A]

/-- The complementary idempotent of a cut. -/
def shadow (p : A) : A := 1 - p

/-- The `p,p` corner of an element relative to the cut. -/
def thesis (p ω : A) : A := p * ω * p

/-- The `shadow,p` corner, directed out of the selected sector. -/
def outward (p ω : A) : A := shadow p * ω * p

/-- The `p,shadow` corner, directed back into the selected sector. -/
def inward (p ω : A) : A := p * ω * shadow p

/-- The `shadow,shadow` corner. -/
def ground (p ω : A) : A := shadow p * ω * shadow p

/-- The bridge formed by the two off-diagonal corners. -/
def bridge (p ω : A) : A := outward p ω + inward p ω

/-- The symmetric round-trip operator, the anticommutator of the two
off-diagonal corners. -/
def sharedGravity (p ω : A) : A :=
  outward p ω * inward p ω + inward p ω * outward p ω

/-- The diagonal truncation that keeps the two within-sector corners and
omits the off-diagonal bridge. -/
def diagonalTruncation (p ω : A) : A :=
  (2 * thesis p ω - p) + (2 * ground p ω - shadow p)

/-- The reciprocal operator associated to an idempotent totality. -/
def reciprocalTotality (ω : A) : A := 2 * ω - 1

/-- Orthogonality and idempotency of the complementary cut. -/
theorem shadow_cut_laws (p : A) (hp : p * p = p) :
    shadow p * shadow p = shadow p ∧ p * shadow p = 0 ∧
      shadow p * p = 0 ∧ p + shadow p = 1 := by
  unfold shadow
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring [hp]

/-- Exact decomposition of an element into its four cut corners. -/
theorem four_corner_decomposition (p ω : A) :
    ω = thesis p ω + outward p ω + inward p ω + ground p ω := by
  unfold thesis outward inward ground shadow
  noncomm_ring

/-- Both off-diagonal Peirce corners square to zero. -/
theorem offDiagonal_square_zero (p ω : A) (hp : p * p = p) :
    outward p ω * outward p ω = 0 ∧ inward p ω * inward p ω = 0 := by
  constructor
  · unfold outward
    have hpq := (shadow_cut_laws p hp).2.1
    calc
      shadow p * ω * p * (shadow p * ω * p) =
          shadow p * ω * (p * shadow p) * ω * p := by noncomm_ring
      _ = 0 := by rw [hpq]; simp
  · unfold inward
    have hqp := (shadow_cut_laws p hp).2.2.1
    calc
      p * ω * shadow p * (p * ω * shadow p) =
          p * ω * (shadow p * p) * ω * shadow p := by noncomm_ring
      _ = 0 := by rw [hqp]; simp

/-- If the totality is idempotent, its selected diagonal defect is the
inward-after-outward round trip. -/
theorem thesis_idempotency_defect (p ω : A)
    (hp : p * p = p) (hω : ω * ω = ω) :
    thesis p ω - thesis p ω * thesis p ω = inward p ω * outward p ω := by
  have hsum : p + shadow p = 1 := (shadow_cut_laws p hp).2.2.2
  have hcorner : p * ω * p = p * ω * p * ω * p +
      p * ω * shadow p * ω * p := by
    calc
      p * ω * p = p * (ω * ω) * p := by rw [hω]
      _ = p * ω * (p + shadow p) * ω * p := by rw [hsum]; noncomm_ring
      _ = p * ω * p * ω * p + p * ω * shadow p * ω * p := by noncomm_ring
  change p * ω * p - (p * ω * p) * (p * ω * p) =
    (p * ω * shadow p) * (shadow p * ω * p)
  have hTmul : (p * ω * p) * (p * ω * p) = p * ω * p * ω * p := by
    calc
      (p * ω * p) * (p * ω * p) = p * ω * (p * p) * ω * p := by noncomm_ring
      _ = p * ω * p * ω * p := by rw [hp]
  have hRmul : (p * ω * shadow p) * (shadow p * ω * p) =
      p * ω * shadow p * ω * p := by
    calc
      (p * ω * shadow p) * (shadow p * ω * p) =
          p * ω * (shadow p * shadow p) * ω * p := by noncomm_ring
      _ = p * ω * shadow p * ω * p := by
        rw [(shadow_cut_laws p hp).1]
  rw [hTmul, hRmul, sub_eq_iff_eq_add]
  calc
    p * ω * p = p * ω * p * ω * p + p * ω * shadow p * ω * p := hcorner
    _ = p * ω * shadow p * ω * p + p * ω * p * ω * p := by ac_rfl

/-- If the totality is idempotent, the complementary diagonal defect is the
outward-after-inward round trip. -/
theorem ground_idempotency_defect (p ω : A)
    (hp : p * p = p) (hω : ω * ω = ω) :
    ground p ω - ground p ω * ground p ω = outward p ω * inward p ω := by
  have hsum : p + shadow p = 1 := (shadow_cut_laws p hp).2.2.2
  have hcorner : shadow p * ω * shadow p =
      shadow p * ω * shadow p * ω * shadow p +
        shadow p * ω * p * ω * shadow p := by
    calc
      shadow p * ω * shadow p = shadow p * (ω * ω) * shadow p := by rw [hω]
      _ = shadow p * ω * (p + shadow p) * ω * shadow p := by rw [hsum]; noncomm_ring
      _ = shadow p * ω * p * ω * shadow p +
        shadow p * ω * shadow p * ω * shadow p := by noncomm_ring
      _ = shadow p * ω * shadow p * ω * shadow p +
        shadow p * ω * p * ω * shadow p := by ac_rfl
  unfold ground inward outward
  change shadow p * ω * shadow p -
      (shadow p * ω * shadow p) * (shadow p * ω * shadow p) =
    (shadow p * ω * p) * (p * ω * shadow p)
  have hGmul : (shadow p * ω * shadow p) * (shadow p * ω * shadow p) =
      shadow p * ω * shadow p * ω * shadow p := by
    calc
      (shadow p * ω * shadow p) * (shadow p * ω * shadow p) =
          shadow p * ω * (shadow p * shadow p) * ω * shadow p := by noncomm_ring
      _ = shadow p * ω * shadow p * ω * shadow p := by
        rw [(shadow_cut_laws p hp).1]
  have hRmul : (shadow p * ω * p) * (p * ω * shadow p) =
      shadow p * ω * p * ω * shadow p := by
    calc
      (shadow p * ω * p) * (p * ω * shadow p) =
          shadow p * ω * (p * p) * ω * shadow p := by noncomm_ring
      _ = shadow p * ω * p * ω * shadow p := by rw [hp]
  rw [hGmul, hRmul, sub_eq_iff_eq_add]
  calc
    shadow p * ω * shadow p =
        shadow p * ω * shadow p * ω * shadow p +
          shadow p * ω * p * ω * shadow p := hcorner
    _ = shadow p * ω * p * ω * shadow p +
        shadow p * ω * shadow p * ω * shadow p := by ac_rfl

/-- Squaring the bridge gives the shared sum of the two ordered
round-trips. -/
theorem bridge_square_eq_sharedGravity (p ω : A) (hp : p * p = p) :
    bridge p ω * bridge p ω = sharedGravity p ω := by
  have h := offDiagonal_square_zero p ω hp
  unfold bridge sharedGravity
  simp only [add_mul, mul_add, h.1, h.2, zero_add]
  ac_rfl

private theorem thesis_absorbs_left (p ω : A) (hp : p * p = p) :
    p * thesis p ω = thesis p ω := by
  unfold thesis
  calc
    p * (p * ω * p) = (p * p) * ω * p := by noncomm_ring
    _ = p * ω * p := by rw [hp]

private theorem thesis_absorbs_right (p ω : A) (hp : p * p = p) :
    thesis p ω * p = thesis p ω := by
  unfold thesis
  calc
    (p * ω * p) * p = p * ω * (p * p) := by noncomm_ring
    _ = p * ω * p := by rw [hp]

private theorem ground_absorbs_left (p ω : A) (hp : p * p = p) :
    shadow p * ground p ω = ground p ω := by
  have hq := (shadow_cut_laws p hp).1
  unfold ground
  calc
    shadow p * (shadow p * ω * shadow p) =
        (shadow p * shadow p) * ω * shadow p := by noncomm_ring
    _ = shadow p * ω * shadow p := by rw [hq]

private theorem ground_absorbs_right (p ω : A) (hp : p * p = p) :
    ground p ω * shadow p = ground p ω := by
  have hq := (shadow_cut_laws p hp).1
  unfold ground
  calc
    (shadow p * ω * shadow p) * shadow p =
        shadow p * ω * (shadow p * shadow p) := by noncomm_ring
    _ = shadow p * ω * shadow p := by rw [hq]

private theorem thesis_ground_mul_zero (p ω : A) (hp : p * p = p) :
    thesis p ω * ground p ω = 0 := by
  have hpq := (shadow_cut_laws p hp).2.1
  unfold thesis ground
  calc
    (p * ω * p) * (shadow p * ω * shadow p) =
        p * ω * (p * shadow p) * ω * shadow p := by noncomm_ring
    _ = 0 := by rw [hpq]; simp

private theorem ground_thesis_mul_zero (p ω : A) (hp : p * p = p) :
    ground p ω * thesis p ω = 0 := by
  have hqp := (shadow_cut_laws p hp).2.2.1
  unfold thesis ground
  calc
    (shadow p * ω * shadow p) * (p * ω * p) =
        shadow p * ω * (shadow p * p) * ω * p := by noncomm_ring
    _ = 0 := by rw [hqp]; simp

/-- The square of the selected diagonal block is its cut idempotent minus
four times the selected diagonal defect. -/
private theorem thesis_truncation_square (p ω : A) (hp : p * p = p) :
    (2 * thesis p ω - p) * (2 * thesis p ω - p) =
      p - 4 * (thesis p ω - thesis p ω * thesis p ω) := by
  have hleft := thesis_absorbs_left p ω hp
  have hright := thesis_absorbs_right p ω hp
  calc
    (2 * thesis p ω - p) * (2 * thesis p ω - p) =
        4 * (thesis p ω * thesis p ω) - 2 * (thesis p ω * p) -
          2 * (p * thesis p ω) + p * p := by noncomm_ring
    _ = 4 * (thesis p ω * thesis p ω) - 4 * thesis p ω + p := by
      rw [hright, hleft, hp]
      noncomm_ring
    _ = p - 4 * (thesis p ω - thesis p ω * thesis p ω) := by noncomm_ring

/-- The square of the ground diagonal block is its cut idempotent minus
four times the ground diagonal defect. -/
private theorem ground_truncation_square (p ω : A) (hp : p * p = p) :
    (2 * ground p ω - shadow p) * (2 * ground p ω - shadow p) =
      shadow p - 4 * (ground p ω - ground p ω * ground p ω) := by
  have hcut := shadow_cut_laws p hp
  have hleft := ground_absorbs_left p ω hp
  have hright := ground_absorbs_right p ω hp
  simp [shadow] at hcut hleft hright ⊢
  calc
    (2 * ground p ω - (1 - p)) * (2 * ground p ω - (1 - p)) =
        4 * (ground p ω * ground p ω) -
          2 * (ground p ω * (1 - p)) -
          2 * ((1 - p) * ground p ω) + (1 - p) * (1 - p) := by noncomm_ring
    _ = 4 * (ground p ω * ground p ω) - 4 * ground p ω + (1 - p) := by
      rw [hright, hleft, hcut.1]
      noncomm_ring
    _ = (1 - p) - 4 * (ground p ω - ground p ω * ground p ω) := by noncomm_ring

/-- The two diagonal truncation blocks annihilate in either order. -/
private theorem diagonal_truncation_blocks_mul_zero (p ω : A)
    (hp : p * p = p) :
    (2 * thesis p ω - p) * (2 * ground p ω - shadow p) = 0 ∧
      (2 * ground p ω - shadow p) * (2 * thesis p ω - p) = 0 := by
  have hpq := (shadow_cut_laws p hp).2.1
  have hqp := (shadow_cut_laws p hp).2.2.1
  have hTG := thesis_ground_mul_zero p ω hp
  have hGT := ground_thesis_mul_zero p ω hp
  have hTq : thesis p ω * shadow p = 0 := by
    unfold thesis
    calc
      p * ω * p * shadow p = p * ω * (p * shadow p) := by noncomm_ring
      _ = 0 := by rw [hpq]; simp
  have hqT : shadow p * thesis p ω = 0 := by
    unfold thesis
    calc
      shadow p * (p * ω * p) = (shadow p * p) * ω * p := by noncomm_ring
      _ = 0 := by rw [hqp]; simp
  have hpG : p * ground p ω = 0 := by
    unfold ground
    calc
      p * (shadow p * ω * shadow p) = (p * shadow p) * ω * shadow p := by noncomm_ring
      _ = 0 := by rw [hpq]; simp
  have hGp : ground p ω * p = 0 := by
    unfold ground
    calc
      (shadow p * ω * shadow p) * p = shadow p * ω * (shadow p * p) := by noncomm_ring
      _ = 0 := by rw [hqp]; simp
  constructor
  · calc
      (2 * thesis p ω - p) * (2 * ground p ω - shadow p) =
          4 * (thesis p ω * ground p ω) -
            2 * (thesis p ω * shadow p) - 2 * (p * ground p ω) +
            p * shadow p := by noncomm_ring
      _ = 0 := by rw [hTG, hTq, hpG, hpq]; simp
  · calc
      (2 * ground p ω - shadow p) * (2 * thesis p ω - p) =
          4 * (ground p ω * thesis p ω) -
            2 * (ground p ω * p) - 2 * (shadow p * thesis p ω) +
            shadow p * p := by noncomm_ring
      _ = 0 := by rw [hGT, hGp, hqT, hqp]; simp

/-- The global defect of the diagonal truncation is exactly four times the
shared two-way round-trip operator. -/
theorem diagonalTruncation_square_defect (p ω : A)
    (hp : p * p = p) (hω : ω * ω = ω) :
    1 - diagonalTruncation p ω * diagonalTruncation p ω =
      4 * sharedGravity p ω := by
  have hblocks := diagonal_truncation_blocks_mul_zero p ω hp
  have hT := thesis_idempotency_defect p ω hp hω
  have hG := ground_idempotency_defect p ω hp hω
  have hsum := (shadow_cut_laws p hp).2.2.2
  unfold diagonalTruncation sharedGravity
  simp only [add_mul, mul_add, hblocks.1, hblocks.2, zero_add, add_zero]
  rw [thesis_truncation_square p ω hp, ground_truncation_square p ω hp]
  rw [hT, hG]
  rw [hsum.symm]
  noncomm_ring

/-- Restoring twice the omitted off-diagonal bridge reconstructs the
reciprocal operator of the totality. -/
theorem reciprocalTotality_eq_diagonalTruncation_add_two_bridge
    (p ω : A) :
    reciprocalTotality ω = diagonalTruncation p ω + 2 * bridge p ω := by
  have hdecomp := four_corner_decomposition p ω
  unfold reciprocalTotality diagonalTruncation bridge thesis ground outward inward shadow
  rw [hdecomp]
  noncomm_ring

/-- An idempotent totality produces an involution under the affine
transformation `ω ↦ 2ω - 1`. -/
theorem reciprocalTotality_involution (ω : A) (hω : ω * ω = ω) :
    reciprocalTotality ω * reciprocalTotality ω = 1 := by
  unfold reciprocalTotality
  noncomm_ring [hω]

end InfoGeometry.Algebra.IdempotentCutAporia
