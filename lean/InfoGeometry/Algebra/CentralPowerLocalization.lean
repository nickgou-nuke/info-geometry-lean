/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic

/-!
# Central-power localization with its additive direct-limit representatives

The carrier is Mathlib's Ore localization of a possibly noncommutative ring.
Only the element being inverted is central. Zero divisors are allowed; the
canonical map has precisely the power-torsion kernel proved below.

The representative `[k,x]` means `x / s^k`. Multiplication adds the two stage
indices and retains the ordered numerator product. These are not ring bonding
maps: multiplication by `s` is the bonding map of the underlying additive
groups (equivalently, integer modules).
-/

namespace InfoGeometry.Algebra.CentralPowerLocalization

open OreLocalization

variable {B : Type*} [Ring B]

/-- Every power of a central element commutes with arbitrary numerators. -/
theorem power_commute (s : B) [h : Fact (∀ x : B, Commute s x)]
    (n : ℕ) (x : B) : Commute (s ^ n) x :=
  (h.out x).pow_left n

/-- Centrality holds for each denominator, including nonregular ones. -/
theorem denominator_commute (s : B) [Fact (∀ x : B, Commute s x)]
    (t : Submonoid.powers s) (x : B) : Commute (t : B) x := by
  rcases t.property with ⟨n, hn⟩
  rw [← hn]
  exact power_commute s n x

/-- Powers of a central element are an Ore set without a cancellation
assumption. In particular this includes singular localization. -/
instance powersOreSet (s : B) [Fact (∀ x : B, Commute s x)] :
    OreSet (Submonoid.powers s) where
  ore_right_cancel x y t h :=
    ⟨t, by rw [(denominator_commute s t x).eq,
      (denominator_commute s t y).eq]; exact h⟩
  oreNum x _ := x
  oreDenom _ t := t
  ore_eq x t := (denominator_commute s t x).eq

/-- The native noncommutative localization at the powers of `s`. -/
abbrev Away (s : B) [Fact (∀ x : B, Commute s x)] :=
  OreLocalization (Submonoid.powers s) B

variable (s : B) [Fact (∀ x : B, Commute s x)]

/-- The stage representative `x / s^k`. -/
def repr (k : ℕ) (x : B) : Away s :=
  x /ₒ Submonoid.pow s k

/-- The actual canonical ring homomorphism; it need not be injective. -/
abbrev of : B →+* Away s := OreLocalization.numeratorRingHom

@[simp] theorem repr_zero (x : B) : repr s 0 x = of s x := by
  have h : Submonoid.pow s 0 = (1 : Submonoid.powers s) := Subtype.ext (pow_zero s)
  simp only [repr, h]
  rfl

@[simp] theorem repr_zero_numerator (k : ℕ) : repr s k 0 = 0 :=
  OreLocalization.zero_oreDiv _

/-- Ordered convolution multiplication on representatives. -/
theorem repr_mul (k l : ℕ) (x y : B) :
    repr s k x * repr s l y = repr s (k + l) (x * y) := by
  unfold repr
  rw [oreDiv_mul_char x y (Submonoid.pow s k) (Submonoid.pow s l)
    x (Submonoid.pow s l) (power_commute s l x).eq]
  congr 1
  apply Subtype.ext
  change s ^ l * s ^ k = s ^ (k + l)
  rw [← pow_add, Nat.add_comm]

/-- Addition uses a common denominator; no numerator commutativity is used. -/
theorem repr_add (k l : ℕ) (x y : B) :
    repr s k x + repr s l y =
      repr s (k + l) (s ^ l * x + s ^ k * y) := by
  unfold repr
  rw [oreDiv_add_char (Submonoid.pow s k) (Submonoid.pow s l)
    (s ^ k) (Submonoid.pow s l) (by
      change s ^ l * s ^ k = s ^ k * s ^ l
      exact (power_commute s l (s ^ k)).eq)]
  simp only [Submonoid.smul_def, smul_eq_mul]
  congr 1
  apply Subtype.ext
  change s ^ l * s ^ k = s ^ (k + l)
  rw [← pow_add, Nat.add_comm]

/-- Equal-stage representatives are additive. -/
theorem repr_add_same (k : ℕ) (x y : B) :
    repr s k (x + y) = repr s k x + repr s k y :=
  OreLocalization.add_oreDiv.symm

/-- A stage transition multiplies the numerator by the same power by which
the denominator is enlarged. -/
theorem repr_bond (k n : ℕ) (x : B) :
    repr s k x = repr s (k + n) (s ^ n * x) := by
  unfold repr
  rw [OreLocalization.expand' x (Submonoid.pow s k) (Submonoid.pow s n)]
  simp only [Submonoid.smul_def, smul_eq_mul]
  congr 1
  apply Subtype.ext
  change s ^ n * s ^ k = s ^ (k + n)
  rw [← pow_add, Nat.add_comm]

/-- Fractions with central denominators agree exactly after a further
denominator multiplication of the cross products. -/
theorem fraction_eq_iff_cross (x y : B) (a b : Submonoid.powers s) :
    (x /ₒ a : Away s) = y /ₒ b ↔
      ∃ t : Submonoid.powers s,
        (t : B) * ((b : B) * x) = (t : B) * ((a : B) * y) := by
  rw [oreDiv_eq_iff]
  constructor
  · rintro ⟨t, v, hn, hd⟩
    simp only [Submonoid.smul_def, smul_eq_mul] at hn
    refine ⟨t, ?_⟩
    calc
      (t : B) * ((b : B) * x) = ((t : B) * b) * x := (mul_assoc _ _ _).symm
      _ = (v * (a : B)) * x := by rw [hd]
      _ = (a : B) * (v * x) := by rw [← (denominator_commute s a v).eq, mul_assoc]
      _ = (a : B) * ((t : B) * y) := by rw [hn]
      _ = (t : B) * ((a : B) * y) := by
        rw [← mul_assoc, (denominator_commute s a (t : B)).eq, mul_assoc]
  · rintro ⟨t, h⟩
    refine ⟨t * a, (t : B) * b, ?_, ?_⟩
    · simpa only [Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul,
        mul_assoc] using h.symm
    · simp only [Submonoid.coe_mul, mul_assoc]
      rw [(denominator_commute s a (b : B)).eq]

/-- Explicit equality criterion for the numerator/stage presentation. -/
theorem repr_eq_iff (k l : ℕ) (x y : B) :
    repr s k x = repr s l y ↔
      ∃ n : ℕ, s ^ (n + l) * x = s ^ (n + k) * y := by
  rw [repr, repr, fraction_eq_iff_cross]
  constructor
  · rintro ⟨t, ht⟩
    rcases t.property with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change (t : B) * (s ^ l * x) = (t : B) * (s ^ k * y) at ht
    simpa only [← hn, pow_add, mul_assoc] using ht
  · rintro ⟨n, hn⟩
    refine ⟨Submonoid.pow s n, ?_⟩
    change s ^ n * (s ^ l * x) = s ^ n * (s ^ k * y)
    simpa only [pow_add, mul_assoc] using hn

/-- Native fraction equality is precisely eventual equality in the directed
additive system with bonding map `x ↦ s*x`. -/
theorem repr_eq_iff_common_stage (k l : ℕ) (x y : B) :
    repr s k x = repr s l y ↔
      ∃ m : ℕ, k ≤ m ∧ l ≤ m ∧
        s ^ (m - k) * x = s ^ (m - l) * y := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (repr_eq_iff s k l x y).mp h
    refine ⟨n + k + l, by omega, by omega, ?_⟩
    have hk : n + k + l - k = n + l := by omega
    have hl : n + k + l - l = n + k := by omega
    simpa only [hk, hl] using hn
  · rintro ⟨m, hk, hl, h⟩
    calc
      repr s k x = repr s m (s ^ (m - k) * x) := by
        simpa only [Nat.add_sub_of_le hk] using repr_bond s k (m - k) x
      _ = repr s m (s ^ (m - l) * y) := congrArg (repr s m) h
      _ = repr s l y := by
        simpa only [Nat.add_sub_of_le hl] using (repr_bond s l (m - l) y).symm

/-- Every element of the native localization has a stage representative. -/
theorem exists_repr (q : Away s) : ∃ k : ℕ, ∃ x : B, repr s k x = q := by
  induction q using OreLocalization.ind with
  | _ x t =>
    rcases t.property with ⟨k, hk⟩
    refine ⟨k, x, ?_⟩
    unfold repr
    congr 1
    exact Subtype.ext hk

/-- The exact kernel consists of elements annihilated by a denominator power. -/
theorem of_eq_zero_iff (x : B) :
    of s x = 0 ↔ ∃ n : ℕ, s ^ n * x = 0 := by
  have h := repr_eq_iff s 0 0 x 0
  simpa only [repr_zero, map_zero, Nat.add_zero, mul_zero] using h

/-- An annihilated element is erased by singular localization. -/
theorem of_eq_zero_of_mul_eq_zero (x : B) (hx : s * x = 0) : of s x = 0 :=
  (of_eq_zero_iff s x).mpr ⟨1, by simpa only [pow_one] using hx⟩

omit [Fact (∀ x : B, Commute s x)] in
/-- Regularity of the single bonding map implies regularity of all its powers. -/
theorem power_mul_eq_zero (hreg : ∀ x : B, s * x = 0 → x = 0)
    (n : ℕ) (x : B) (hx : s ^ n * x = 0) : x = 0 := by
  induction n generalizing x with
  | zero => simpa only [pow_zero, one_mul] using hx
  | succ n ih =>
    apply ih
    apply hreg
    simpa only [pow_succ', mul_assoc] using hx

/-- The canonical homomorphism is faithful whenever multiplication by `s`
has trivial kernel. No global invertibility of `s` is assumed. -/
theorem of_injective (hreg : ∀ x : B, s * x = 0 → x = 0) :
    Function.Injective (of s) := by
  intro x y h
  have hz : of s (x - y) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (of_eq_zero_iff s (x - y)).mp hz
  exact sub_eq_zero.mp (power_mul_eq_zero s hreg n (x - y) hn)

/-- Nonzero torsion witnesses the failure of faithfulness. -/
theorem not_injective_of_annihilator (x : B) (hx : x ≠ 0) (hsx : s * x = 0) :
    ¬ Function.Injective (of s) := by
  intro hi
  apply hx
  apply hi
  rw [map_zero]
  exact of_eq_zero_of_mul_eq_zero s x hsx

/-- The inverse is an internal quotient element, not an additional input. -/
def inverse : Away s := repr s 1 1

/-- The internally constructed denominator inverse is a right inverse. -/
theorem of_mul_inverse : of s s * inverse s = 1 := by
  change (s /ₒ (1 : Submonoid.powers s)) *
    ((1 : B) /ₒ Submonoid.pow s 1) = 1
  simpa only [Submonoid.pow_apply, pow_one, Submonoid.coe_one] using
    (OreLocalization.mul_inv (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s) 1)

/-- The same quotient element is a left inverse. -/
theorem inverse_mul_of : inverse s * of s s = 1 := by
  change ((1 : B) /ₒ Submonoid.pow s 1) *
    (s /ₒ (1 : Submonoid.powers s)) = 1
  simpa only [Submonoid.pow_apply, pow_one, Submonoid.coe_one] using
    (OreLocalization.mul_inv (1 : Submonoid.powers s)
      (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s))

/-- Native Ore universal factorization into any ring in which all denominator
powers map to units. -/
noncomputable def lift {C : Type*} [Ring C] (f : B →+* C)
    (u : Submonoid.powers s →* Units C)
    (hu : ∀ t : Submonoid.powers s, f t = u t) : Away s →+* C :=
  OreLocalization.universalHom f u hu

/-- The constructed lift extends the given ring homomorphism. -/
theorem lift_of {C : Type*} [Ring C] (f : B →+* C)
    (u : Submonoid.powers s →* Units C)
    (hu : ∀ t : Submonoid.powers s, f t = u t) (x : B) :
    lift s f u hu (of s x) = f x :=
  OreLocalization.universalHom_commutes f u hu

/-- This ring factorization is unique. -/
theorem lift_unique {C : Type*} [Ring C] (f : B →+* C)
    (u : Submonoid.powers s →* Units C)
    (hu : ∀ t : Submonoid.powers s, f t = u t)
    (g : Away s →+* C) (hg : ∀ x : B, g (of s x) = f x) :
    g = lift s f u hu :=
  OreLocalization.universalHom_unique f u hu g hg

/-- Inverting the single generator is the complete condition for unique
ring factorization. No compatible family of denominator units is assumed. -/
theorem existsUnique_lift_of_isUnit {C : Type*} [Ring C]
    (f : B →+* C) (hs : IsUnit (f s)) :
    ∃! g : Away s →+* C, ∀ x : B, g (of s x) = f x := by
  let fden : Submonoid.powers s →* C :=
    f.toMonoidHom.comp (Submonoid.powers s).subtype
  have hu : ∀ t : Submonoid.powers s, IsUnit (fden t) := by
    intro t
    rcases t.property with ⟨n, hn⟩
    change IsUnit (f (t : B))
    rw [← hn, map_pow]
    exact hs.pow n
  let u : Submonoid.powers s →* Units C := IsUnit.liftRight fden hu
  have huf : ∀ t : Submonoid.powers s, f t = u t := by
    intro t
    exact (IsUnit.coe_liftRight fden hu t).symm
  refine ⟨lift s f u huf, lift_of s f u huf, ?_⟩
  intro g hg
  exact lift_unique s f u huf g hg

end InfoGeometry.Algebra.CentralPowerLocalization
