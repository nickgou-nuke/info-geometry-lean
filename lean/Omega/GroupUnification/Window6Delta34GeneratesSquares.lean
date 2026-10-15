import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace Omega.GroupUnification

instance : Fact (Nat.Prime 571) := ⟨by norm_num⟩

/-- The window-6 boundary uplift `δ = 34` viewed as a unit of `ZMod 571`. -/
def delta34Unit571 : (ZMod 571)ˣ :=
  Units.mk0 (34 : ZMod 571) (by decide)

/-- An explicit square root of `34` modulo `571`. -/
def delta34Sqrt571 : (ZMod 571)ˣ :=
  Units.mk0 (264 : ZMod 571) (by decide)

/-- The subgroup of squares inside `(ZMod 571)ˣ`. -/
def squareUnitsSubgroup571 : Subgroup (ZMod 571)ˣ where
  carrier := {u | ∃ v : (ZMod 571)ˣ, v ^ (2 : ℕ) = u}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x * y, by simp [pow_two, mul_comm, mul_left_comm]⟩
  inv_mem' := by
    rintro a ⟨x, rfl⟩
    refine ⟨x⁻¹, by simp [pow_two]⟩

private theorem delta34Sqrt571_sq :
    delta34Sqrt571 ^ (2 : ℕ) = delta34Unit571 := by
  ext
  decide

private theorem prime_dvd_285 {p : ℕ} (hp : Nat.Prime p) (hpdvd : p ∣ 285) :
    p = 3 ∨ p = 5 ∨ p = 19 := by
  have hmul : p ∣ 3 * (5 * 19) := by
    norm_num at hpdvd ⊢
    exact hpdvd
  rcases hp.dvd_mul.mp hmul with h3 | hrest
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp h3)
  · rcases hp.dvd_mul.mp hrest with h5 | h19
    · exact Or.inr <| Or.inl <|
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h5
    · exact Or.inr <| Or.inr <|
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19)).mp h19

private theorem nat34_pow_2 : 34 ^ 2 ≡ 14 [MOD 571] := by
  norm_num [Nat.ModEq]

private theorem nat34_pow_4 : 34 ^ 4 ≡ 196 [MOD 571] := by
  calc
    34 ^ 4 ≡ 14 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat34_pow_2
    _ ≡ 196 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_8 : 34 ^ 8 ≡ 159 [MOD 571] := by
  calc
    34 ^ 8 ≡ 196 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat34_pow_4
    _ ≡ 159 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_16 : 34 ^ 16 ≡ 157 [MOD 571] := by
  calc
    34 ^ 16 ≡ 159 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat34_pow_8
    _ ≡ 157 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_32 : 34 ^ 32 ≡ 96 [MOD 571] := by
  calc
    34 ^ 32 ≡ 157 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat34_pow_16
    _ ≡ 96 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_64 : 34 ^ 64 ≡ 80 [MOD 571] := by
  calc
    34 ^ 64 ≡ 96 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat34_pow_32
    _ ≡ 80 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_128 : 34 ^ 128 ≡ 119 [MOD 571] := by
  calc
    34 ^ 128 ≡ 80 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat34_pow_64
    _ ≡ 119 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_256 : 34 ^ 256 ≡ 457 [MOD 571] := by
  calc
    34 ^ 256 ≡ 119 ^ 2 [MOD 571] := Nat.ModEq.pow 2 nat34_pow_128
    _ ≡ 457 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_285 : 34 ^ 285 ≡ 1 [MOD 571] := by
  have hexp : 285 = 256 + 16 + 8 + 4 + 1 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add, Nat.pow_one]
  calc
    34 ^ 256 * 34 ^ 16 * 34 ^ 8 * 34 ^ 4 * 34 ≡
        457 * 157 * 159 * 196 * 34 [MOD 571] := by
      exact (((nat34_pow_256.mul nat34_pow_16).mul nat34_pow_8).mul nat34_pow_4).mul
        (Nat.ModEq.rfl)
    _ ≡ 1 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_95 : 34 ^ 95 ≡ 461 [MOD 571] := by
  have hexp : 95 = 64 + 16 + 8 + 4 + 2 + 1 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add, Nat.pow_one]
  calc
    34 ^ 64 * 34 ^ 16 * 34 ^ 8 * 34 ^ 4 * 34 ^ 2 * 34 ≡
        80 * 157 * 159 * 196 * 14 * 34 [MOD 571] := by
      exact (((((nat34_pow_64.mul nat34_pow_16).mul nat34_pow_8).mul
        nat34_pow_4).mul nat34_pow_2).mul Nat.ModEq.rfl)
    _ ≡ 461 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_57 : 34 ^ 57 ≡ 387 [MOD 571] := by
  have hexp : 57 = 32 + 16 + 8 + 1 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add, Nat.pow_one]
  calc
    34 ^ 32 * 34 ^ 16 * 34 ^ 8 * 34 ≡ 96 * 157 * 159 * 34 [MOD 571] := by
      exact ((nat34_pow_32.mul nat34_pow_16).mul nat34_pow_8).mul Nat.ModEq.rfl
    _ ≡ 387 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_15 : 34 ^ 15 ≡ 55 [MOD 571] := by
  have hexp : 15 = 8 + 4 + 2 + 1 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add, Nat.pow_one]
  calc
    34 ^ 8 * 34 ^ 4 * 34 ^ 2 * 34 ≡ 159 * 196 * 14 * 34 [MOD 571] := by
      exact ((nat34_pow_8.mul nat34_pow_4).mul nat34_pow_2).mul Nat.ModEq.rfl
    _ ≡ 55 [MOD 571] := by norm_num [Nat.ModEq]

private theorem nat34_pow_154 : 34 ^ 154 ≡ 144 [MOD 571] := by
  have hexp : 154 = 128 + 16 + 8 + 2 := by norm_num
  rw [hexp]
  simp only [Nat.pow_add]
  calc
    34 ^ 128 * 34 ^ 16 * 34 ^ 8 * 34 ^ 2 ≡
        119 * 157 * 159 * 14 [MOD 571] := by
      exact ((nat34_pow_128.mul nat34_pow_16).mul nat34_pow_8).mul nat34_pow_2
    _ ≡ 144 [MOD 571] := by norm_num [Nat.ModEq]

private theorem natCast34_eq_zmod34 : ((34 : ℕ) : ZMod 571) = (34 : ZMod 571) := by
  norm_num

private theorem zmod34_pow_285 : (34 : ZMod 571) ^ 285 = 1 := by
  have hcast : ((34 ^ 285 : ℕ) : ZMod 571) = 1 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat34_pow_285
  have hpow : ((34 : ℕ) : ZMod 571) ^ 285 = 1 := by
    simpa only [Nat.cast_pow] using hcast
  rw [natCast34_eq_zmod34] at hpow
  exact hpow

private theorem zmod34_pow_95 : (34 : ZMod 571) ^ 95 = 461 := by
  have hcast : ((34 ^ 95 : ℕ) : ZMod 571) = 461 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat34_pow_95
  have hpow : ((34 : ℕ) : ZMod 571) ^ 95 = 461 := by
    simpa only [Nat.cast_pow] using hcast
  rw [natCast34_eq_zmod34] at hpow
  exact hpow

private theorem zmod34_pow_57 : (34 : ZMod 571) ^ 57 = 387 := by
  have hcast : ((34 ^ 57 : ℕ) : ZMod 571) = 387 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat34_pow_57
  have hpow : ((34 : ℕ) : ZMod 571) ^ 57 = 387 := by
    simpa only [Nat.cast_pow] using hcast
  rw [natCast34_eq_zmod34] at hpow
  exact hpow

private theorem zmod34_pow_15 : (34 : ZMod 571) ^ 15 = 55 := by
  have hcast : ((34 ^ 15 : ℕ) : ZMod 571) = 55 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat34_pow_15
  have hpow : ((34 : ℕ) : ZMod 571) ^ 15 = 55 := by
    simpa only [Nat.cast_pow] using hcast
  rw [natCast34_eq_zmod34] at hpow
  exact hpow

/-- The residue `55` is the fifteenth power of the certified order-285 unit `34`. -/
theorem delta34_pow15_eq_55 : (34 : ZMod 571) ^ 15 = 55 := zmod34_pow_15

/-- The residue `144` is the 154th power of the certified order-285 unit `34`. -/
theorem delta34_pow154_eq_144 : (34 : ZMod 571) ^ 154 = 144 := by
  have hcast : ((34 ^ 154 : ℕ) : ZMod 571) = 144 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 nat34_pow_154
  have hpow : ((34 : ℕ) : ZMod 571) ^ 154 = 144 := by
    simpa only [Nat.cast_pow] using hcast
  rw [natCast34_eq_zmod34] at hpow
  exact hpow

private theorem order_delta34Unit571 :
    orderOf delta34Unit571 = 285 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := delta34Unit571) (n := 285)
    (by norm_num) ?_ ?_
  · apply Units.ext
    exact zmod34_pow_285
  · intro p hp hpdvd
    rcases prime_dvd_285 hp hpdvd with h3 | h5 | h19
    · subst p
      intro h
      have hv := congrArg (fun u : (ZMod 571)ˣ => (u : ZMod 571)) h
      have hv' : (34 : ZMod 571) ^ 95 = 1 := by simpa [delta34Unit571] using hv
      rw [zmod34_pow_95] at hv'
      have hmod := (ZMod.natCast_eq_natCast_iff' 461 1 571).mp hv'
      norm_num at hmod
    · subst p
      intro h
      have hv := congrArg (fun u : (ZMod 571)ˣ => (u : ZMod 571)) h
      have hv' : (34 : ZMod 571) ^ 57 = 1 := by simpa [delta34Unit571] using hv
      rw [zmod34_pow_57] at hv'
      have hmod := (ZMod.natCast_eq_natCast_iff' 387 1 571).mp hv'
      norm_num at hmod
    · subst p
      intro h
      have hv := congrArg (fun u : (ZMod 571)ˣ => (u : ZMod 571)) h
      have hv' : (34 : ZMod 571) ^ 15 = 1 := by simpa [delta34Unit571] using hv
      rw [zmod34_pow_15] at hv'
      have hmod := (ZMod.natCast_eq_natCast_iff' 55 1 571).mp hv'
      norm_num at hmod

private theorem delta34_power_is_square (n : ℕ) :
    ∃ u : (ZMod 571)ˣ, u ^ (2 : ℕ) = delta34Unit571 ^ n := by
  refine ⟨delta34Sqrt571 ^ n, ?_⟩
  calc
    (delta34Sqrt571 ^ n) ^ (2 : ℕ) = delta34Sqrt571 ^ (n * 2) := by rw [pow_mul]
    _ = delta34Sqrt571 ^ (2 * n) := by rw [Nat.mul_comm]
    _ = (delta34Sqrt571 ^ (2 : ℕ)) ^ n := by rw [pow_mul]
    _ = delta34Unit571 ^ n := by rw [delta34Sqrt571_sq]

/-- The window-6 uplift step `δ = 34` has exact order `285 = (571 - 1) / 2`, so its cyclic
subgroup has index two in `(ZMod 571)ˣ`. Since `34 = 264² (mod 571)`, every power of `34`
is a square, matching the paper's square-subgroup certificate.
    prop:window6-delta34-generates-squares -/
theorem paper_window6_delta34_generates_squares :
    orderOf delta34Unit571 = 285 ∧
    Fintype.card (Subgroup.zpowers delta34Unit571) = 285 ∧
    Fintype.card (Subgroup.zpowers delta34Unit571) * 2 = Fintype.card (ZMod 571)ˣ ∧
    delta34Unit571 ∈ squareUnitsSubgroup571 ∧
    (∀ n : ℕ, delta34Unit571 ^ n ∈ squareUnitsSubgroup571) := by
  refine ⟨order_delta34Unit571, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_zpowers, order_delta34Unit571]
  · rw [Fintype.card_zpowers, order_delta34Unit571]
    rw [ZMod.card_units_eq_totient, Nat.totient_prime (by norm_num : Nat.Prime 571)]
  · exact ⟨delta34Sqrt571, delta34Sqrt571_sq⟩
  · intro n
    exact delta34_power_is_square n

end Omega.GroupUnification
