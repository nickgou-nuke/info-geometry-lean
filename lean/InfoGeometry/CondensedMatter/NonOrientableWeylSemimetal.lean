import Mathlib

/-!
# Non-orientable Weyl semimetal finite charge corridor

This module records a small theorem-safe bridge inspired by
Douwes--Stålhammar, *Twisted (co)homology of non-orientable Weyl semimetals*,
arXiv:2511.22303v2.

The paper develops a coordinate-free twisted (co)homology classification of
non-orientable Brillouin zones and recovers mod-2 Weyl charge cancellation.  We
do **not** formalize that full classification here.  Instead, we isolate the
finite algebraic shadow needed by the current codebase:

* a two-node glide orbit;
* ordinary oriented integer cancellation;
* same-sign cancellation after reducing charges modulo two;
* the exact-sequence consequence `im β ⊆ ker Σ` as an explicit conditional
  theorem, where `Σ` is the total-charge readout into `ZMod 2`.

#### BUCKET 1: CLOSED FINITE THEOREMS

`glideFlip_involutive`, `oriented_pair_charge_cancels`,
`nonorientable_mod_two_charge_cancels`,
`same_integer_charge_mod_two_cancels`,
`orientation_reversal_invisible_mod_two`,
`totalChargeModTwo_orientation_reversal_invariant`, and
`totalChargeModTwo_local_orientation_choice_invariant`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

`exactness_gives_mod_two_charge_cancellation` depends on the named premise
`ExactAtLocalCharges β`, the finite substitute for the paper's exactness claim
at the local charge group.

#### BUCKET 3: OPEN CLOSURE DEBT

The full twisted homology/cohomology exact sequences, the computation
`H^3(K^2 × S^1) ≃ Z_2`, Poincaré duality with local coefficients, and the
classification of all non-orientable Brillouin zones remain outside this finite
module.
-/

noncomputable section

namespace NonOrientableWeylSemimetal

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
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc
    nonOrientableWeylCharge 0 + nonOrientableWeylCharge 1 = (1 : ZMod 2) + 1 := by
      simp [nonOrientableWeylCharge]
    _ = (2 : ZMod 2) := by norm_num
    _ = 0 := h2

/-- More generally, two equal integer charges vanish after reduction modulo two. -/
theorem same_integer_charge_mod_two_cancels (q : ℤ) :
    ((q : ZMod 2) + (q : ZMod 2)) = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc
    (q : ZMod 2) + (q : ZMod 2) = (2 : ZMod 2) * (q : ZMod 2) := by ring
    _ = 0 := by rw [h2, zero_mul]

/--
Modulo two, changing the local orientation of a Weyl charge does not change the
charge readout. This is the finite algebraic reason the paper's non-orientable
total charge lands in `Z₂`: `χ` and `-χ` are indistinguishable mod two.
-/
theorem orientation_reversal_invisible_mod_two (q : ℤ) :
    ((-q : ℤ) : ZMod 2) = (q : ZMod 2) := by
  rw [Int.cast_neg]
  exact neg_eq_of_add_eq_zero_left (same_integer_charge_mod_two_cancels q)

/-- The coordinate-free total-charge readout `Σ : ℤ^k → Z₂`. -/
def totalChargeModTwo {ι : Type} [Fintype ι] (charge : ι → ℤ) : ZMod 2 :=
  ∑ i, (charge i : ZMod 2)

/-- The local kernel condition `Σ(charge) = 0`. -/
def ModTwoChargeNeutral {ι : Type} [Fintype ι] (charge : ι → ℤ) : Prop :=
  totalChargeModTwo charge = 0

/-- Multiplication by a local orientation sign `±1` is invisible modulo two. -/
theorem orientation_sign_mul_invisible_mod_two {s q : ℤ}
    (hs : s = 1 ∨ s = -1) :
    ((s * q : ℤ) : ZMod 2) = (q : ZMod 2) := by
  rcases hs with h | h
  · rw [h]
    simp
  · rw [h]
    simp

/--
The total mod-two charge is independent of reversing every local orientation.
This is a finite coordinate-free shadow of the paper's statement that a choice
of local orientation at each Weyl point cannot change the `Z₂` total charge.
-/
theorem totalChargeModTwo_orientation_reversal_invariant
    {ι : Type} [Fintype ι] (charge : ι → ℤ) :
    totalChargeModTwo (fun i => -charge i) = totalChargeModTwo charge := by
  unfold totalChargeModTwo
  refine Finset.sum_congr rfl ?_
  intro i _
  exact orientation_reversal_invisible_mod_two (charge i)

/--
The total mod-two charge is independent of an arbitrary local orientation basis:
each individual charge may be replaced by either `χᵢ` or `-χᵢ` without changing
`Σ`.  This is the finite algebraic content of the paper's statement that the
map `Σ : ℤᵏ → ℤ₂` is basis-independent because `χ ≡ -χ (mod 2)`.
-/
theorem totalChargeModTwo_local_orientation_choice_invariant
    {ι : Type} [Fintype ι] (charge : ι → ℤ) (sign : ι → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1) :
    totalChargeModTwo (fun i => sign i * charge i) = totalChargeModTwo charge := by
  unfold totalChargeModTwo
  exact Finset.sum_congr rfl
    (fun i _ => orientation_sign_mul_invisible_mod_two (hsign i))

/--
Finite exactness socket for the semimetal charge map.

If `β : Semimetal → ι → ℤ` sends semimetal data to local Weyl charges, this is
the exactness consequence `im β ⊆ ker Σ`, where `Σ` is `totalChargeModTwo`.
-/
def ExactAtLocalCharges {Semimetal ι : Type} [Fintype ι]
    (β : Semimetal → ι → ℤ) : Prop :=
  ∀ s, ModTwoChargeNeutral (β s)

/--
Conditional form of the Douwes--Stålhammar mod-two cancellation step.

Once the relevant twisted Mayer--Vietoris sequence supplies exactness at the
local charge group, every semimetal charge configuration in the image of `β`
has zero total charge in `ZMod 2`.
-/
theorem exactness_gives_mod_two_charge_cancellation
    {Semimetal ι : Type} [Fintype ι]
    (β : Semimetal → ι → ℤ)
    (hExact : ExactAtLocalCharges β)
    (s : Semimetal) :
    ModTwoChargeNeutral (β s) :=
  hExact s

/-- A compact certificate bundling orientable and non-orientable finite cancellation. -/
theorem finite_glide_orbit_charge_cancellation_packet (q : ℤ) :
    (∑ i : Fin 2, orientedWeylCharge q i) = 0 ∧
      (∑ i : Fin 2, nonOrientableWeylCharge i) = 0 ∧
        ((q : ZMod 2) + (q : ZMod 2)) = 0 := by
  exact ⟨oriented_pair_charge_cancels q,
    nonorientable_mod_two_charge_cancels,
    same_integer_charge_mod_two_cancels q⟩

/-- Reversing the local orientation at every site leaves the finite packet unchanged mod two. -/
theorem totalChargeModTwo_pointwise_orientation_invariant
    {ι : Type} [Fintype ι] (charge : ι → ℤ)
    (sign : ι → ℤ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1) :
    totalChargeModTwo (fun i => sign i * charge i) = totalChargeModTwo charge := by
  unfold totalChargeModTwo
  exact Finset.sum_congr rfl
    (fun i _ => orientation_sign_mul_invisible_mod_two (q := charge i) (hsign i))

end NonOrientableWeylSemimetal

end noncomputable section
