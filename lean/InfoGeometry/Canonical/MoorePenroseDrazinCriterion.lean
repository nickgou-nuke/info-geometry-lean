/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MoorePenroseDrazinObstruction
import InfoGeometry.Canonical.DrazinSpectralFittingBridge

/-!
# Exact Drazin-index criteria for a Moore–Penrose inverse

The two predicates retain their native arbitrary star-ring carrier. Positive
Drazin witness indices are equivalent to commutation; zero is equivalent to
two-sided invertibility. Indices here are witnesses, not minimal indices.
-/

namespace InfoGeometry.Canonical.MoorePenroseDrazinCriterion

open Drazin MoorePenrose DrazinSpectralFittingBridge

variable {R : Type*} [Ring R] [StarRing R] {a b : R}

theorem index_one_iff_commute (h : IsMoorePenroseInverse a b) :
    IsDrazinInverse a b 1 ↔ Commute a b := by
  constructor
  · intro hd
    exact hd.comm
  · intro hc
    exact moore_penrose_is_drazin_index_one ⟨h.aba_eq_a, h.bab_eq_b, hc.eq⟩

theorem positive_index_iff_commute (h : IsMoorePenroseInverse a b)
    {k : ℕ} (hk : 1 ≤ k) : IsDrazinInverse a b k ↔ Commute a b := by
  constructor
  · intro hd
    exact hd.comm
  · intro hc
    have hd := (index_one_iff_commute h).2 hc
    exact ⟨hd.comm, hd.idempotent, hd.power_le hk⟩

theorem index_zero_iff_two_sided_inverse (h : IsMoorePenroseInverse a b) :
    IsDrazinInverse a b 0 ↔ a * b = 1 ∧ b * a = 1 := by
  constructor
  · intro hd
    have hab : a * b = 1 := by simpa using hd.power
    exact ⟨hab, hd.comm.symm.trans hab⟩
  · rintro ⟨hab, hba⟩
    exact ⟨hab.trans hba.symm, h.bab_eq_b, by simpa using hab⟩

theorem exists_index_iff_commute (h : IsMoorePenroseInverse a b) :
    (∃ k : ℕ, IsDrazinInverse a b k) ↔ Commute a b := by
  constructor
  · rintro ⟨k, hd⟩
    exact hd.comm
  · intro hc
    exact ⟨1, (index_one_iff_commute h).2 hc⟩

end InfoGeometry.Canonical.MoorePenroseDrazinCriterion
