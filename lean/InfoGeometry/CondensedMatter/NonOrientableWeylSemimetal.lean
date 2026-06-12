import Mathlib

/-!
# Non-orientable Weyl semimetal finite charge corridor

This module records a small theorem-safe bridge inspired by
Douwes--Stålhammar, *Twisted (co)homology of non-orientable Weyl semimetals*,
arXiv:2511.22303v2.

The paper develops a coordinate-free twisted (co)homology classification of
non-orientable Brillouin zones and recovers mod-2 Weyl charge cancellation.  We
do **not** formalize that full classification here.  Instead, we isolate the
finite algebraic shadow needed by the current codebase: a two-node glide orbit,
ordinary oriented integer cancellation, and same-sign cancellation after reducing
charges modulo two.
-/

noncomputable section

namespace InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal

open scoped BigOperators

/-- A two-node glide orbit, representing the simplest momentum-space glide pair. -/
def glideFlip (i : Fin 2) : Fin 2 :=
  if i = 0 then 1 else 0

@[simp]
theorem glideFlip_zero : glideFlip 0 = 1 := by
  simp [glideFlip]

@[simp]
theorem glideFlip_one : glideFlip 1 = 0 := by
  simp [glideFlip]

/-- The finite glide flip is a genuine involution. -/
@[simp]
theorem glideFlip_involutive (i : Fin 2) : glideFlip (glideFlip i) = i := by
  fin_cases i <;> simp

/-- In an orientable two-node pair, opposite integer Weyl charges cancel. -/
def orientedWeylCharge (q : ℤ) : Fin 2 → ℤ
  | 0 => q
  | 1 => -q

/-- Integer charge cancellation for the ordinary orientable pair. -/
theorem oriented_pair_charge_cancels (q : ℤ) :
    (∑ i : Fin 2, orientedWeylCharge q i) = 0 := by
  simp [Fin.sum_univ_two, orientedWeylCharge]

/--
In the non-orientable finite shadow, both glide partners carry the same local
unit charge, but the meaningful total readout is mod two.
-/
def nonOrientableWeylCharge : Fin 2 → ZMod 2 :=
  fun _ => 1

/-- The two same-sign glide charges cancel in `ZMod 2`. -/
theorem nonorientable_mod_two_charge_cancels :
    (∑ i : Fin 2, nonOrientableWeylCharge i) = 0 := by
  rw [Fin.sum_univ_two]
  native_decide

/-- More generally, two equal integer charges vanish after reduction modulo two. -/
theorem same_integer_charge_mod_two_cancels (q : ℤ) :
    ((q : ZMod 2) + (q : ZMod 2)) = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by native_decide
  calc
    (q : ZMod 2) + (q : ZMod 2) = (2 : ZMod 2) * (q : ZMod 2) := by ring
    _ = 0 := by rw [h2, zero_mul]

/-- A compact certificate bundling orientable and non-orientable finite cancellation. -/
theorem finite_glide_orbit_charge_cancellation_packet (q : ℤ) :
    (∑ i : Fin 2, orientedWeylCharge q i) = 0 ∧
      (∑ i : Fin 2, nonOrientableWeylCharge i) = 0 ∧
        ((q : ZMod 2) + (q : ZMod 2)) = 0 := by
  exact ⟨oriented_pair_charge_cancels q,
    nonorientable_mod_two_charge_cancels,
    same_integer_charge_mod_two_cancels q⟩

end InfoGeometry.CondensedMatter.NonOrientableWeylSemimetal

end noncomputable section
