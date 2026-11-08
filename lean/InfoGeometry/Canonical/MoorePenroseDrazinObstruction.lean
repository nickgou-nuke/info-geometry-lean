/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.MoorePenrose

/-!
# A general Moore--Penrose/Drazin obstruction

The Moore--Penrose equations do not imply the Drazin laws at any index for a
nonzero nilpotent element. Its unique Drazin inverse is zero, which cannot
also be an inner inverse. The square-zero/index-one case follows in particular.
This is stated over an
arbitrary unital ring (with the star-ring structure needed only for the
Moore--Penrose predicate), so it does not depend on coordinates or a
commutative model.
-/

namespace InfoGeometry.Canonical.MoorePenroseDrazinObstruction

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose

variable {R : Type*} [Ring R]

/-- Zero is a Drazin inverse at precisely the exponents that annihilate the
operator. The exponent need not be the minimal nilpotency index. -/
theorem drazin_zero_iff_power_zero (a : R) (k : ℕ) :
    IsDrazinInverse a 0 k ↔ a ^ k = 0 := by
  simp [IsDrazinInverse, eq_comm]

/-- Nilpotency determines the Drazin inverse uniquely, even when the witness
uses a different index from the supplied annihilating exponent. -/
theorem nilpotent_drazin_inverse_eq_zero {a b : R} {n k : ℕ}
    (hn : a ^ n = 0) (hD : IsDrazinInverse a b k) : b = 0 := by
  exact hD.unique_of_indices ((drazin_zero_iff_power_zero a n).2 hn)

/-- Exact classification of all Drazin witnesses of a nilpotent operator. -/
theorem nilpotent_drazin_iff {a b : R} {n k : ℕ} (hn : a ^ n = 0) :
    IsDrazinInverse a b k ↔ b = 0 ∧ a ^ k = 0 := by
  constructor
  · intro hD
    have hb := nilpotent_drazin_inverse_eq_zero hn hD
    subst b
    exact ⟨rfl, (drazin_zero_iff_power_zero a k).1 hD⟩
  · rintro ⟨rfl, hk⟩
    exact (drazin_zero_iff_power_zero a k).2 hk

/-- Contract: in any associative unital ring, an inner inverse of a nonzero
nilpotent element cannot also satisfy the Drazin laws, at any index.
No star, positivity, or finite-dimensionality assumption is needed. -/
theorem nilpotent_inner_inverse_not_drazin
    {a b : R} {n : ℕ} (hinner : a * b * a = a)
    (hn : a ^ n = 0) (ha0 : a ≠ 0) (k : ℕ) :
    ¬ IsDrazinInverse a b k := by
  intro hD
  have hb := nilpotent_drazin_inverse_eq_zero hn hD
  rw [hb, mul_zero, zero_mul] at hinner
  exact ha0 hinner.symm

/-- The index-one Drazin power law forces a square-zero element to vanish. -/
theorem square_zero_eq_zero_of_drazin_index_one
    {a b : R} (hD : IsDrazinInverse a b 1) (ha : a * a = 0) : a = 0 := by
  have hpow := hD.power
  exact (by simpa [pow_two, pow_one, ha] using hpow.symm)

variable [StarRing R]

/-- A nonzero nilpotent operator's Moore--Penrose inverse cannot be its
Drazin inverse at any index. -/
theorem nilpotent_moore_penrose_not_drazin
    {a b : R} {n : ℕ} (hMP : IsMoorePenroseInverse a b)
    (hn : a ^ n = 0) (ha0 : a ≠ 0) (k : ℕ) :
    ¬ IsDrazinInverse a b k :=
  nilpotent_inner_inverse_not_drazin hMP.aba_eq_a hn ha0 k

/-- A nonzero square-zero Moore--Penrose operator cannot be Drazin index one
    with the same inverse.  Thus an EP/commutation hypothesis is genuinely
    necessary in the usual Moore--Penrose-to-Drazin implication. -/
theorem square_zero_moore_penrose_not_drazin_index_one
    {a b : R} (hMP : IsMoorePenroseInverse a b)
    (ha : a * a = 0) (ha0 : a ≠ 0) :
    ¬ IsDrazinInverse a b 1 := by
  rcases hMP with ⟨hinner, houter, hleft, hright⟩
  intro hD
  exact ha0 (square_zero_eq_zero_of_drazin_index_one hD ha)

end InfoGeometry.Canonical.MoorePenroseDrazinObstruction
