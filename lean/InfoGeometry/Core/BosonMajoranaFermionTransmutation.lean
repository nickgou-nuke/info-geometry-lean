/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.BosonParityString
import InfoGeometry.Core.DiracSuperalgebra

/-!
# Jordan–Wigner Majoranas, star compatibility, and naturality

The two split-signature generators square to `1` and `-1`. They are not called
unipotent. Star statements require the explicit duality `B j = star (d j)`.
Doubled chiral identities do not divide by two, including in characteristic two.
This is an algebraic construction on ordered finite families, not a
spin–statistics theorem or a central-extension/isomorphism assertion.
-/
namespace InfoGeometry.Core.BosonParityString.IsCommutingBosonSystem

open InfoGeometry.Core.DiracSuperalgebra

variable {A : Type*} [Ring A] {N : ℕ} {d B : Fin N → A}
variable (h : IsCommutingBosonSystem d B)

/-- The positive split-signature Majorana of the dressed pair. -/
def plus (j : Fin N) : A := majoranaPlus (h.dressed false j) (h.dressed true j)

/-- The negative split-signature Majorana of the dressed pair. -/
def minus (j : Fin N) : A := majoranaMinus (h.dressed false j) (h.dressed true j)

lemma plus_eq_string (j : Fin N) : h.plus j = h.parityString j * (d j + B j) :=
  (mul_add _ _ _).symm

lemma minus_eq_string (j : Fin N) : h.minus j = h.parityString j * (d j - B j) :=
  (mul_sub _ _ _).symm

lemma chiral_combinations (j : Fin N) :
    h.plus j + h.minus j = 2 • h.dressed false j ∧
    h.plus j - h.minus j = 2 • h.dressed true j := by
  simp only [plus, minus, majoranaPlus, majoranaMinus, two_nsmul]
  constructor <;> abel

lemma majorana_squares (j : Fin N) : h.plus j * h.plus j = 1 ∧ h.minus j * h.minus j = -1 := by
  have hc : h.dressed false j * h.dressed true j + h.dressed true j * h.dressed false j = 1 := by
    simpa using h.dressed_mixed_car j j
  constructor
  · calc
      h.plus j * h.plus j = h.dressed false j * h.dressed false j +
          (h.dressed false j * h.dressed true j + h.dressed true j * h.dressed false j) +
          h.dressed true j * h.dressed true j := by
        unfold plus majoranaPlus; noncomm_ring
      _ = 1 := by rw [h.dressed_sq, h.dressed_sq, hc, zero_add, add_zero]
  · calc
      h.minus j * h.minus j = h.dressed false j * h.dressed false j -
          (h.dressed false j * h.dressed true j + h.dressed true j * h.dressed false j) +
          h.dressed true j * h.dressed true j := by
        unfold minus majoranaMinus; noncomm_ring
      _ = -1 := by rw [h.dressed_sq, h.dressed_sq, hc, zero_sub, add_zero]

lemma majorana_mixed_anti (j k : Fin N) : h.plus j * h.minus k + h.minus k * h.plus j = 0 := by
  calc
    h.plus j * h.minus k + h.minus k * h.plus j =
        (h.dressed false j * h.dressed false k + h.dressed false k * h.dressed false j) -
        (h.dressed true j * h.dressed true k + h.dressed true k * h.dressed true j) +
        (h.dressed false k * h.dressed true j + h.dressed true j * h.dressed false k) -
        (h.dressed false j * h.dressed true k + h.dressed true k * h.dressed false j) := by
      unfold plus minus majoranaPlus majoranaMinus; noncomm_ring
    _ = 0 := by
      rw [h.dressed_self_car, h.dressed_self_car, h.dressed_mixed_car, h.dressed_mixed_car]
      simp only [eq_comm, sub_self, zero_add]

lemma majorana_same_sign_anti {j k : Fin N} (hne : j ≠ k) :
    h.plus j * h.plus k + h.plus k * h.plus j = 0 ∧
    h.minus j * h.minus k + h.minus k * h.minus j = 0 := by
  have hdd := h.dressed_anti false false hne
  have hBB := h.dressed_anti true true hne
  have hdB := h.dressed_anti false true hne
  have hBd := h.dressed_anti true false hne
  constructor
  · calc
      h.plus j * h.plus k + h.plus k * h.plus j =
          (h.dressed false j * h.dressed false k + h.dressed false k * h.dressed false j) +
          (h.dressed true j * h.dressed true k + h.dressed true k * h.dressed true j) +
          (h.dressed false j * h.dressed true k + h.dressed true k * h.dressed false j) +
          (h.dressed true j * h.dressed false k + h.dressed false k * h.dressed true j) := by
        unfold plus majoranaPlus; noncomm_ring
      _ = 0 := by rw [hdd, hBB, hdB, hBd]; simp
  · calc
      h.minus j * h.minus k + h.minus k * h.minus j =
          (h.dressed false j * h.dressed false k + h.dressed false k * h.dressed false j) +
          (h.dressed true j * h.dressed true k + h.dressed true k * h.dressed true j) -
          (h.dressed false j * h.dressed true k + h.dressed true k * h.dressed false j) -
          (h.dressed true j * h.dressed false k + h.dressed false k * h.dressed true j) := by
        unfold minus majoranaMinus; noncomm_ring
      _ = 0 := by rw [hdd, hBB, hdB, hBd]; simp

lemma majorana_product (j : Fin N) : h.minus j * h.plus j = parity d B j := by
  calc
    h.minus j * h.plus j = h.dressed false j * h.dressed false j +
        (h.dressed false j * h.dressed true j - h.dressed true j * h.dressed false j) -
        h.dressed true j * h.dressed true j := by
      unfold minus plus majoranaMinus majoranaPlus; noncomm_ring
    _ = parity d B j := by rw [h.dressed_sq, h.dressed_sq, h.dressed_parity, zero_add, sub_zero]

section Star
variable [StarRing A] (hdual : ∀ j, B j = star (d j))
include hdual

lemma parity_star (j : Fin N) : IsSelfAdjoint (parity d B j) := by
  change star (d j * B j - B j * d j) = d j * B j - B j * d j
  simp only [hdual, star_sub, star_mul, star_star]

lemma product_star (s : Finset (Fin N)) : IsSelfAdjoint (h.parityProduct s) := by
  induction s using Finset.induction_on with
  | empty => exact IsSelfAdjoint.one A
  | @insert j s hj ih =>
    have hs : h.parityProduct (insert j s) = parity d B j * h.parityProduct s :=
      Finset.noncommProd_insert_of_notMem s j _ _ hj
    change star (h.parityProduct (insert j s)) = h.parityProduct (insert j s)
    rw [hs, star_mul, ih.star_eq, (parity_star hdual j).star_eq]
    exact (h.product_commutes_parity s j).eq

lemma dressed_star (j : Fin N) : star (h.dressed false j) = h.dressed true j := by
  change star (h.parityString j * d j) = h.parityString j * B j
  rw [star_mul, ← hdual j]
  change B j * star (h.parityProduct (Finset.Iio j)) = h.parityProduct (Finset.Iio j) * B j
  rw [(h.product_star hdual (Finset.Iio j)).star_eq]
  exact (h.string_mode_commute true (j := j) le_rfl).eq.symm

lemma majorana_star (j : Fin N) : IsSelfAdjoint (h.plus j) ∧ star (h.minus j) = -h.minus j :=
  majorana_star_symmetry (h.dressed_star hdual j).symm

/-- With adjoint duality the dressed pair satisfies the existing four Penrose equations. -/
lemma dressed_penrose (j : Fin N) :
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
      (h.dressed false j) (h.dressed true j) := by
  have hc : h.dressed false j * h.dressed true j + h.dressed true j * h.dressed false j = 1 := by
    simpa using h.dressed_mixed_car j j
  have hs := h.dressed_star hdual j
  have ht : star (h.dressed true j) = h.dressed false j := by rw [← hs, star_star]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have H := congrArg (fun x => x * h.dressed false j) hc
    simpa only [add_mul, mul_assoc, h.dressed_sq, mul_zero, add_zero, one_mul] using H
  · have H := congrArg (fun x => x * h.dressed true j) hc
    simpa only [add_mul, mul_assoc, h.dressed_sq, mul_zero, zero_add, one_mul] using H
  · rw [star_mul, hs, ht]
  · rw [star_mul, hs, ht]

end Star

section Naturality
variable {C : Type*} [Ring C]
include h

/-- Transport the input system along a native unital ring homomorphism. -/
theorem map (f : A →+* C) : IsCommutingBosonSystem (f ∘ d) (f ∘ B) where
  d_sq j := by simpa only [Function.comp_apply, ← map_mul, map_zero] using congrArg f (h.d_sq j)
  B_sq j := by simpa only [Function.comp_apply, ← map_mul, map_zero] using congrArg f (h.B_sq j)
  on_site j := by simpa only [Function.comp_apply, ← map_mul, ← map_add, map_one] using congrArg f (h.on_site j)
  comm_dd hne := (h.comm_dd hne).map f
  comm_BB hne := (h.comm_BB hne).map f
  comm_dB hne := (h.comm_dB hne).map f

lemma map_product (f : A →+* C) (s : Finset (Fin N)) :
    f (h.parityProduct s) = (h.map f).parityProduct s := by
  calc
    f (h.parityProduct s) = s.noncommProd (fun i => f (parity d B i))
        (fun i _ j _ _ => (h.parity_commute i j).map f) :=
      Finset.map_noncommProd s (parity d B) (fun i _ j _ _ => h.parity_commute i j) f
    _ = (h.map f).parityProduct s :=
      Finset.noncommProd_congr rfl (fun i _ => by simp [parity]) _

lemma map_dressed (f : A →+* C) (c : Bool) (j : Fin N) :
    f (h.dressed c j) = (h.map f).dressed c j := by
  unfold dressed parityString
  rw [map_mul, h.map_product]
  cases c <;> rfl

lemma map_majorana (f : A →+* C) (j : Fin N) :
    f (h.plus j) = (h.map f).plus j ∧ f (h.minus j) = (h.map f).minus j := by
  simp only [plus, minus, majoranaPlus, majoranaMinus, map_add, map_sub, h.map_dressed,
    and_self]

end Naturality
end InfoGeometry.Core.BosonParityString.IsCommutingBosonSystem
