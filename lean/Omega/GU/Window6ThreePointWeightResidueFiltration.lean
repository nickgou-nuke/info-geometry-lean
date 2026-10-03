import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic
import Omega.GU.Window6BdryUpliftResidueStratification

namespace Omega.GU

private def unit21 : (ZMod 571)ˣ :=
  Units.mk0 (21 : ZMod 571) (by
    intro h
    have hdvd : 571 ∣ 21 := (ZMod.natCast_eq_zero_iff 21 571).mp h
    omega)

-- Repeated-squaring residues are the small certificate for the order proof.
private theorem nat21_pow2 : 21 ^ 2 ≡ 441 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow4 : 21 ^ 4 ≡ 341 [MOD 571] := by
  calc 21 ^ 4 ≡ 441 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat21_pow2
    _ ≡ 341 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow8 : 21 ^ 8 ≡ 368 [MOD 571] := by
  calc 21 ^ 8 ≡ 341 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat21_pow4
    _ ≡ 368 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow16 : 21 ^ 16 ≡ 97 [MOD 571] := by
  calc 21 ^ 16 ≡ 368 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat21_pow8
    _ ≡ 97 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow32 : 21 ^ 32 ≡ 273 [MOD 571] := by
  calc 21 ^ 32 ≡ 97 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat21_pow16
    _ ≡ 273 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow64 : 21 ^ 64 ≡ 299 [MOD 571] := by
  calc 21 ^ 64 ≡ 273 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat21_pow32
    _ ≡ 299 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow128 : 21 ^ 128 ≡ 325 [MOD 571] := by
  calc 21 ^ 128 ≡ 299 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat21_pow64
    _ ≡ 325 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow256 : 21 ^ 256 ≡ 561 [MOD 571] := by
  calc 21 ^ 256 ≡ 325 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat21_pow128
    _ ≡ 561 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow285 : 21 ^ 285 ≡ 1 [MOD 571] := by
  have hexp : 285 = 256 + 16 + 8 + 4 + 1 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add, Nat.pow_one]
  calc
    21 ^ 256 * 21 ^ 16 * 21 ^ 8 * 21 ^ 4 * 21 ≡
        561 * 97 * 368 * 341 * 21 [MOD 571] := by
      exact ((((nat21_pow256.mul nat21_pow16).mul nat21_pow8).mul nat21_pow4).mul
        Nat.ModEq.rfl)
    _ ≡ 1 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow95 : 21 ^ 95 ≡ 461 [MOD 571] := by
  have hexp : 95 = 64 + 16 + 8 + 4 + 2 + 1 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add, Nat.pow_one]
  calc
    21 ^ 64 * 21 ^ 16 * 21 ^ 8 * 21 ^ 4 * 21 ^ 2 * 21 ≡
        299 * 97 * 368 * 341 * 441 * 21 [MOD 571] := by
      exact (((((nat21_pow64.mul nat21_pow16).mul nat21_pow8).mul nat21_pow4).mul
        nat21_pow2).mul Nat.ModEq.rfl)
    _ ≡ 461 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow57 : 21 ^ 57 ≡ 481 [MOD 571] := by
  have hexp : 57 = 32 + 16 + 8 + 1 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add, Nat.pow_one]
  calc
    21 ^ 32 * 21 ^ 16 * 21 ^ 8 * 21 ≡ 273 * 97 * 368 * 21 [MOD 571] := by
      exact (((nat21_pow32.mul nat21_pow16).mul nat21_pow8).mul Nat.ModEq.rfl)
    _ ≡ 481 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow15 : 21 ^ 15 ≡ 59 [MOD 571] := by
  have hexp : 15 = 8 + 4 + 2 + 1 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add, Nat.pow_one]
  calc
    21 ^ 8 * 21 ^ 4 * 21 ^ 2 * 21 ≡ 368 * 341 * 441 * 21 [MOD 571] := by
      exact ((nat21_pow8.mul nat21_pow4).mul nat21_pow2).mul Nat.ModEq.rfl
    _ ≡ 59 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat21_pow30 : 21 ^ 30 ≡ 55 [MOD 571] := by
  have hexp : 30 = 16 + 8 + 4 + 2 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add]
  calc
    21 ^ 16 * 21 ^ 8 * 21 ^ 4 * 21 ^ 2 ≡ 97 * 368 * 341 * 441 [MOD 571] := by
      exact ((nat21_pow16.mul nat21_pow8).mul nat21_pow4).mul nat21_pow2
    _ ≡ 55 [MOD 571] := by norm_num [Nat.ModEq]

private theorem zmod21_pow285 : (21 : ZMod 571) ^ 285 = 1 := by
  have hcast : ((21 ^ 285 : ℕ) : ZMod 571) = 1 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat21_pow285
  simpa only [Nat.cast_pow] using hcast

private theorem zmod21_pow95 : (21 : ZMod 571) ^ 95 = 461 := by
  have hcast : ((21 ^ 95 : ℕ) : ZMod 571) = 461 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat21_pow95
  simpa only [Nat.cast_pow] using hcast

private theorem zmod21_pow57 : (21 : ZMod 571) ^ 57 = 481 := by
  have hcast : ((21 ^ 57 : ℕ) : ZMod 571) = 481 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat21_pow57
  simpa only [Nat.cast_pow] using hcast

private theorem zmod21_pow15 : (21 : ZMod 571) ^ 15 = 59 := by
  have hcast : ((21 ^ 15 : ℕ) : ZMod 571) = 59 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat21_pow15
  simpa only [Nat.cast_pow] using hcast

private theorem zmod21_pow30 : (21 : ZMod 571) ^ 30 = 55 := by
  have hcast : ((21 ^ 30 : ℕ) : ZMod 571) = 55 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat21_pow30
  simpa only [Nat.cast_pow] using hcast

private theorem prime_dvd_285 {p : ℕ} (hp : Nat.Prime p) (hpdvd : p ∣ 285) :
    p = 3 ∨ p = 5 ∨ p = 19 := by
  have hmul : p ∣ 3 * (5 * 19) := by
    simpa [Nat.mul_assoc] using hpdvd
  rcases hp.dvd_mul.mp hmul with h3 | hrest
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3)
  · rcases hp.dvd_mul.mp hrest with h5 | h19
    · exact Or.inr <| Or.inl <| (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h5
    · exact Or.inr <| Or.inr <|
        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19)).mp h19

private theorem order_unit21 : orderOf unit21 = 285 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := unit21) (n := 285) (by norm_num) ?_ ?_
  · apply Units.ext
    exact zmod21_pow285
  · intro p hp hpdvd
    rcases prime_dvd_285 hp hpdvd with rfl | rfl | rfl
    · intro h
      have hc := congrArg (fun u : (ZMod 571)ˣ => (u : ZMod 571)) h
      change (21 : ZMod 571) ^ 95 = 1 at hc
      rw [zmod21_pow95] at hc
      have hmod := (ZMod.natCast_eq_natCast_iff' 461 1 571).mp hc
      norm_num at hmod
    · intro h
      have hc := congrArg (fun u : (ZMod 571)ˣ => (u : ZMod 571)) h
      change (21 : ZMod 571) ^ 57 = 1 at hc
      rw [zmod21_pow57] at hc
      have hmod := (ZMod.natCast_eq_natCast_iff' 481 1 571).mp hc
      norm_num at hmod
    · intro h
      have hc := congrArg (fun u : (ZMod 571)ˣ => (u : ZMod 571)) h
      change (21 : ZMod 571) ^ 15 = 1 at hc
      rw [zmod21_pow15] at hc
      have hmod := (ZMod.natCast_eq_natCast_iff' 59 1 571).mp hc
      norm_num at hmod

private theorem order_zmod21 : orderOf (21 : ZMod 571) = 285 := by
  change orderOf (unit21 : ZMod 571) = 285
  rw [orderOf_units]
  exact order_unit21

/-- The three audited window-6 weights lie in the same residue filtration modulo `571`, with the
    two explicit power relations linking the short orbit to the order-`285` generators.
    cor:window6-three-point-weight-residue-filtration -/
theorem paper_window6_three_point_weight_residue_filtration :
    orderOf (21 : ZMod 571) = 285 ∧
      orderOf (34 : ZMod 571) = 285 ∧
      orderOf (55 : ZMod 571) = 19 ∧
      (55 : ZMod 571) = (34 : ZMod 571) ^ 15 ∧
      (55 : ZMod 571) = (21 : ZMod 571) ^ 30 := by
  rcases paper_window6_bdry_uplift_residue_stratification with ⟨h34, _, h55, _⟩
  exact ⟨order_zmod21, h34, h55,
    Omega.GroupUnification.delta34_pow15_eq_55, zmod21_pow30⟩

end Omega.GU
