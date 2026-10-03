import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic
import Omega.GroupUnification.Window6Delta34GeneratesSquares

namespace Omega.GU

instance factPrime571Window6BdryUpliftResidueStratification : Fact (Nat.Prime 571) := by
  exact ⟨by norm_num⟩

private def unit34 : (ZMod 571)ˣ :=
  Units.mk0 (34 : ZMod 571) (by decide)

private def unit144 : (ZMod 571)ˣ :=
  Units.mk0 (144 : ZMod 571) (by decide)

private def unit55 : (ZMod 571)ˣ :=
  Units.mk0 (55 : ZMod 571) (by decide)

private def unit89 : (ZMod 571)ˣ :=
  Units.mk0 (89 : ZMod 571) (by decide)

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

private theorem prime_dvd_570 {p : ℕ} (hp : Nat.Prime p) (hpdvd : p ∣ 570) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 19 := by
  have hmul : p ∣ 2 * (3 * (5 * 19)) := by
    simpa [Nat.mul_assoc] using hpdvd
  rcases hp.dvd_mul.mp hmul with h2 | hrest
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h2)
  · rcases hp.dvd_mul.mp hrest with h3 | hrest'
    · exact Or.inr <|
        Or.inl <| (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3
    · rcases hp.dvd_mul.mp hrest' with h5 | h19
      · exact Or.inr <| Or.inr <| Or.inl <|
          (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h5
      · exact Or.inr <| Or.inr <| Or.inr <|
          (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19)).mp h19

private theorem nat89_pow_2 : 89 ^ 2 ≡ 498 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_4 : 89 ^ 4 ≡ 190 [MOD 571] := by
  calc 89 ^ 4 ≡ 498 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat89_pow_2
    _ ≡ 190 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_8 : 89 ^ 8 ≡ 127 [MOD 571] := by
  calc 89 ^ 8 ≡ 190 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat89_pow_4
    _ ≡ 127 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_16 : 89 ^ 16 ≡ 141 [MOD 571] := by
  calc 89 ^ 16 ≡ 127 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat89_pow_8
    _ ≡ 141 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_32 : 89 ^ 32 ≡ 467 [MOD 571] := by
  calc 89 ^ 32 ≡ 141 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat89_pow_16
    _ ≡ 467 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_64 : 89 ^ 64 ≡ 538 [MOD 571] := by
  calc 89 ^ 64 ≡ 467 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat89_pow_32
    _ ≡ 538 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_128 : 89 ^ 128 ≡ 518 [MOD 571] := by
  calc 89 ^ 128 ≡ 538 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat89_pow_64
    _ ≡ 518 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_256 : 89 ^ 256 ≡ 525 [MOD 571] := by
  calc 89 ^ 256 ≡ 518 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat89_pow_128
    _ ≡ 525 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_285 : 89 ^ 285 ≡ 570 [MOD 571] := by
  have hexp : 285 = 256 + 16 + 8 + 4 + 1 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add, Nat.pow_one]
  calc
    89 ^ 256 * 89 ^ 16 * 89 ^ 8 * 89 ^ 4 * 89 ≡
        525 * 141 * 127 * 190 * 89 [MOD 571] := by
      exact ((((nat89_pow_256.mul nat89_pow_16).mul nat89_pow_8).mul
        nat89_pow_4).mul Nat.ModEq.rfl)
    _ ≡ 570 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_570 : 89 ^ 570 ≡ 1 [MOD 571] := by
  have hpow := Nat.ModEq.pow 2 nat89_pow_285
  calc
    89 ^ 570 = (89 ^ 285) ^ 2 := by rw [← pow_mul]
    _ ≡ 570 ^ 2 [MOD 571] := hpow
    _ ≡ 1 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_190 : 89 ^ 190 ≡ 461 [MOD 571] := by
  have hexp : 190 = 128 + 32 + 16 + 8 + 4 + 2 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add]
  calc
    89 ^ 128 * 89 ^ 32 * 89 ^ 16 * 89 ^ 8 * 89 ^ 4 * 89 ^ 2 ≡
        518 * 467 * 141 * 127 * 190 * 498 [MOD 571] := by
      exact (((((nat89_pow_128.mul nat89_pow_32).mul nat89_pow_16).mul
        nat89_pow_8).mul nat89_pow_4).mul nat89_pow_2)
    _ ≡ 461 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_114 : 89 ^ 114 ≡ 481 [MOD 571] := by
  have hexp : 114 = 64 + 32 + 16 + 2 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add]
  calc
    89 ^ 64 * 89 ^ 32 * 89 ^ 16 * 89 ^ 2 ≡
        538 * 467 * 141 * 498 [MOD 571] := by
      exact ((nat89_pow_64.mul nat89_pow_32).mul nat89_pow_16).mul nat89_pow_2
    _ ≡ 481 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat89_pow_30 : 89 ^ 30 ≡ 64 [MOD 571] := by
  have hexp : 30 = 16 + 8 + 4 + 2 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add]
  calc
    89 ^ 16 * 89 ^ 8 * 89 ^ 4 * 89 ^ 2 ≡
        141 * 127 * 190 * 498 [MOD 571] := by
      exact ((nat89_pow_16.mul nat89_pow_8).mul nat89_pow_4).mul nat89_pow_2
    _ ≡ 64 [MOD 571] := by norm_num [Nat.ModEq]

private theorem zmod89_pow570 : (89 : ZMod 571) ^ 570 = 1 := by
  have hcast : ((89 ^ 570 : ℕ) : ZMod 571) = 1 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat89_pow_570
  simpa only [Nat.cast_pow] using hcast

private theorem zmod89_pow285 : (89 : ZMod 571) ^ 285 = 570 := by
  have hcast : ((89 ^ 285 : ℕ) : ZMod 571) = 570 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat89_pow_285
  simpa only [Nat.cast_pow] using hcast

private theorem zmod89_pow190 : (89 : ZMod 571) ^ 190 = 461 := by
  have hcast : ((89 ^ 190 : ℕ) : ZMod 571) = 461 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat89_pow_190
  simpa only [Nat.cast_pow] using hcast

private theorem zmod89_pow114 : (89 : ZMod 571) ^ 114 = 481 := by
  have hcast : ((89 ^ 114 : ℕ) : ZMod 571) = 481 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat89_pow_114
  simpa only [Nat.cast_pow] using hcast

private theorem zmod89_pow30 : (89 : ZMod 571) ^ 30 = 64 := by
  have hcast : ((89 ^ 30 : ℕ) : ZMod 571) = 64 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat89_pow_30
  simpa only [Nat.cast_pow] using hcast

private theorem order_unit34 : orderOf unit34 = 285 := by
  have hunit : unit34 = Omega.GroupUnification.delta34Unit571 := by
    apply Units.ext
    rfl
  rw [hunit]
  exact Omega.GroupUnification.paper_window6_delta34_generates_squares.1

private theorem order_unit144 : orderOf unit144 = 285 := by
  have hpow : unit144 = Omega.GroupUnification.delta34Unit571 ^ 154 := by
    apply Units.ext
    change (144 : ZMod 571) = (34 : ZMod 571) ^ 154
    exact Omega.GroupUnification.delta34_pow154_eq_144.symm
  rw [hpow, orderOf_pow, Omega.GroupUnification.paper_window6_delta34_generates_squares.1]
  norm_num [Nat.gcd]

private theorem order_unit55 : orderOf unit55 = 19 := by
  have hpow : unit55 = Omega.GroupUnification.delta34Unit571 ^ 15 := by
    apply Units.ext
    change (55 : ZMod 571) = (34 : ZMod 571) ^ 15
    exact Omega.GroupUnification.delta34_pow15_eq_55.symm
  rw [hpow, orderOf_pow, Omega.GroupUnification.paper_window6_delta34_generates_squares.1]
  norm_num [Nat.gcd]

private theorem order_unit89 : orderOf unit89 = 570 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := unit89) (n := 570) (by decide) ?_ ?_
  · apply Units.ext
    simpa [unit89] using zmod89_pow570
  · intro p hp hpdvd
    rcases prime_dvd_570 hp hpdvd with rfl | rfl | rfl | rfl
    · intro h
      have hv := congrArg (fun u : (ZMod 571)ˣ => (u : ZMod 571)) h
      have hv' : (89 : ZMod 571) ^ 285 = 1 := by simpa [unit89] using hv
      rw [zmod89_pow285] at hv'
      have hmod := (ZMod.natCast_eq_natCast_iff' 570 1 571).mp hv'
      norm_num at hmod
    · intro h
      have hv := congrArg (fun u : (ZMod 571)ˣ => (u : ZMod 571)) h
      have hv' : (89 : ZMod 571) ^ 190 = 1 := by simpa [unit89] using hv
      rw [zmod89_pow190] at hv'
      have hmod := (ZMod.natCast_eq_natCast_iff' 461 1 571).mp hv'
      norm_num at hmod
    · intro h
      have hv := congrArg (fun u : (ZMod 571)ˣ => (u : ZMod 571)) h
      have hv' : (89 : ZMod 571) ^ 114 = 1 := by simpa [unit89] using hv
      rw [zmod89_pow114] at hv'
      have hmod := (ZMod.natCast_eq_natCast_iff' 481 1 571).mp hv'
      norm_num at hmod
    · intro h
      have hv := congrArg (fun u : (ZMod 571)ˣ => (u : ZMod 571)) h
      have hv' : (89 : ZMod 571) ^ 30 = 1 := by simpa [unit89] using hv
      rw [zmod89_pow30] at hv'
      have hmod := (ZMod.natCast_eq_natCast_iff' 64 1 571).mp hv'
      norm_num at hmod

private theorem order_zmod34 : orderOf (34 : ZMod 571) = 285 := by
  change orderOf (unit34 : ZMod 571) = 285
  rw [orderOf_units]
  exact order_unit34

private theorem order_zmod144 : orderOf (144 : ZMod 571) = 285 := by
  change orderOf (unit144 : ZMod 571) = 285
  rw [orderOf_units]
  exact order_unit144

private theorem order_zmod55 : orderOf (55 : ZMod 571) = 19 := by
  change orderOf (unit55 : ZMod 571) = 19
  rw [orderOf_units]
  exact order_unit55

private theorem order_zmod89 : orderOf (89 : ZMod 571) = 570 := by
  change orderOf (unit89 : ZMod 571) = 570
  rw [orderOf_units]
  exact order_unit89

/-- Audited residue-stratification orders for the window-6 boundary uplift modulo `571`.
    prop:window6-bdry-uplift-residue-stratification -/
theorem paper_window6_bdry_uplift_residue_stratification :
    orderOf (34 : ZMod 571) = 285 ∧
      orderOf (144 : ZMod 571) = 285 ∧
      orderOf (55 : ZMod 571) = 19 ∧
      orderOf (89 : ZMod 571) = 570 := by
  exact ⟨order_zmod34, order_zmod144, order_zmod55, order_zmod89⟩

end Omega.GU
