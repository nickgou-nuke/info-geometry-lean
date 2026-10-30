/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

module

public import InfoGeometry.Exceptional.CFSGPort.ModelCatalog

public section

set_option linter.style.haveILetI false

namespace InfoGeometry.Exceptional.CFSGPort

/-- A group modeled on a cyclic group of prime order is simple. -/
theorem isSimpleGroup_of_cyclicPrimeModel {G : Type} [Group G] {p : ℕ}
    (hp : p.Prime)
    (h : Nonempty (G ≃* Multiplicative (ZMod p))) : IsSimpleGroup G := by
  obtain ⟨e⟩ := h
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hs : IsSimpleGroup (Multiplicative (ZMod p)) :=
    isSimpleGroup_of_prime_card (hp := ⟨hp⟩) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  exact e.isSimpleGroup_congr.mpr hs

/-- An alternating-group model of degree at least five is simple. -/
theorem isSimpleGroup_of_alternatingModel {G : Type} [Group G] {n : ℕ}
    (hn : 5 ≤ n)
    (h : Nonempty (G ≃* alternatingGroup (Fin n))) : IsSimpleGroup G := by
  obtain ⟨e⟩ := h
  have hs : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  exact e.isSimpleGroup_congr.mpr hs

end InfoGeometry.Exceptional.CFSGPort

end
