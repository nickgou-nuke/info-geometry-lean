/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Central-power localization and the ambient multiplication obstruction

The relation on degree/numerator pairs is an equivalence for every denominator,
without a centrality or cancellation assumption. For a central denominator its
quotient is realized by Mathlib's native noncommutative Ore localization. Its
ring operations have the expected degree formulas; a self-adjoint denominator
also gives a star-ring. Regularity makes the degree-zero map injective and
identifies the exact obstruction to multiplying equivalent pairs on the left.
-/

namespace InfoGeometry.OperatorAlgebra.CentralPowerLocalization

variable {B : Type*} [Ring B]

/-- Common left multiplication eventually identifies two degree/numerator pairs. -/
def DayRel (s : B) (a b : ℕ × B) : Prop :=
  ∃ m : ℕ, s ^ m * (s ^ b.1 * a.2) = s ^ m * (s ^ a.1 * b.2)

theorem dayRel_refl (s : B) (a : ℕ × B) : DayRel s a a := ⟨0, rfl⟩

theorem dayRel_symm {s : B} {a b : ℕ × B} (h : DayRel s a b) : DayRel s b a := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, hm.symm⟩

/-- Transitivity belongs to the underlying additive directed system, even when
the proposed multiplication does not descend. -/
theorem dayRel_trans {s : B} {a b c : ℕ × B}
    (hab : DayRel s a b) (hbc : DayRel s b c) : DayRel s a c := by
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbc
  refine ⟨m + n + b.1, ?_⟩
  have h₁ := congrArg (fun x : B => s ^ (n + c.1) * x) hm
  have h₂ := congrArg (fun x : B => s ^ (m + a.1) * x) hn
  simp only [← mul_assoc, ← pow_add] at h₁ h₂ ⊢
  simp only [Nat.add_comm, Nat.add_left_comm] at h₁ h₂ ⊢
  exact h₁.trans h₂

def daySetoid (s : B) : Setoid (ℕ × B) where
  r := DayRel s
  iseqv := ⟨dayRel_refl s, dayRel_symm, dayRel_trans⟩

theorem pow_mul_injective {s : B} (hs : Function.Injective (fun x : B => s * x))
    (n : ℕ) : Function.Injective (fun x : B => s ^ n * x) := by
  induction n with
  | zero =>
      intro x y h
      simpa using h
  | succ n ih =>
      intro x y h
      apply ih
      apply hs
      simpa only [pow_succ', mul_assoc] using h

theorem dayRel_iff_cross_eq {s : B}
    (hs : Function.Injective (fun x : B => s * x)) (a b : ℕ × B) :
    DayRel s a b ↔ s ^ b.1 * a.2 = s ^ a.1 * b.2 := by
  constructor
  · rintro ⟨m, hm⟩
    exact pow_mul_injective hs m hm
  · intro h
    exact ⟨0, by simpa using h⟩

theorem dayRel_zero_iff {s : B}
    (hs : Function.Injective (fun x : B => s * x)) (x y : B) :
    DayRel s (0, x) (0, y) ↔ x = y := by
  simpa using dayRel_iff_cross_eq hs (0, x) (0, y)

def dayAdd (s : B) (a b : ℕ × B) : ℕ × B :=
  (a.1 + b.1, s ^ b.1 * a.2 + s ^ a.1 * b.2)

def dayMul (a b : ℕ × B) : ℕ × B := (a.1 + b.1, a.2 * b.2)

def dayStar [StarRing B] (a : ℕ × B) : ℕ × B := (a.1, star a.2)

theorem dayRel_one_shift (s : B) : DayRel s (0, 1) (1, s) := by
  exact ⟨0, by simp⟩

theorem dayRel_numerator_shift (s x : B) : DayRel s (0, x) (1, s * x) := by
  exact ⟨0, by simp⟩

/-- Under left regularity, multiplying the identity relation by `x` is lawful
exactly when `x` commutes with the denominator. -/
theorem dayMul_identity_shift_iff {s : B}
    (hs : Function.Injective (fun x : B => s * x)) (x : B) :
    DayRel s (dayMul (0, x) (0, 1)) (dayMul (0, x) (1, s)) ↔ Commute s x := by
  simpa only [dayMul, Nat.zero_add, mul_one, pow_zero, pow_one, one_mul,
    Commute, SemiconjBy] using dayRel_iff_cross_eq hs (0, x) (1, x * s)

theorem dayMul_not_congruent_of_not_commute {s x : B}
    (hs : Function.Injective (fun y : B => s * y)) (hx : ¬ Commute s x) :
    ¬ DayRel s (dayMul (0, x) (0, 1)) (dayMul (0, x) (1, s)) := by
  exact fun h => hx ((dayMul_identity_shift_iff hs x).mp h)

/-- Star applied to the defining shift relation has the same exact
centralizer obstruction as multiplication. -/
theorem dayStar_numerator_shift_iff [StarRing B] {s : B}
    (hself : star s = s) (hs : Function.Injective (fun y : B => s * y)) (x : B) :
    DayRel s (dayStar (0, x)) (dayStar (1, s * x)) ↔ Commute s x := by
  rw [dayRel_iff_cross_eq hs]
  have hc : Commute s (star x) ↔ Commute s x := by
    simpa only [hself] using (commute_star_star (x := s) (y := x))
  simpa only [dayStar, pow_zero, pow_one, one_mul, star_mul, hself,
    Commute, SemiconjBy] using hc

section Central

variable (s : B) (hs : ∀ x : B, Commute s x)

include hs in
theorem powers_commute (t : Submonoid.powers s) (x : B) : Commute (t : B) x := by
  rcases t with ⟨t, ht⟩
  rcases ht with ⟨n, rfl⟩
  exact (hs x).pow_left n

/-- The Ore data for powers of a central element retain the ambient
noncommutative multiplication. -/
@[instance_reducible]
def centralPowersOreSet : OreLocalization.OreSet (Submonoid.powers s) where
  ore_right_cancel x y t h :=
    ⟨t, (powers_commute s hs t x).eq.trans (h.trans (powers_commute s hs t y).eq.symm)⟩
  oreNum x _ := x
  oreDenom _ t := t
  ore_eq x t := (powers_commute s hs t x).eq

/-- Native Mathlib Ore localization, with the central powers as Ore set. -/
abbrev RingLocalization :=
  @OreLocalization B inferInstance (Submonoid.powers s) (centralPowersOreSet s hs)
    B inferInstance

def powerDenominator (n : ℕ) : Submonoid.powers s := ⟨s ^ n, ⟨n, rfl⟩⟩

@[simp] theorem powerDenominator_coe (n : ℕ) :
    (powerDenominator s n : B) = s ^ n := rfl

theorem powerDenominator_mul (m n : ℕ) :
    powerDenominator s m * powerDenominator s n = powerDenominator s (m + n) := by
  apply Subtype.ext
  exact (pow_add s m n).symm

/-- A degree/numerator pair as an actual Ore fraction. -/
def ofPair (a : ℕ × B) : RingLocalization s hs := by
  letI := centralPowersOreSet s hs
  exact OreLocalization.oreDiv a.2 (powerDenominator s a.1)

theorem ofPair_surjective : Function.Surjective (ofPair s hs) := by
  let := centralPowersOreSet s hs
  intro z
  induction z using OreLocalization.ind with
  | _ x t =>
      rcases t with ⟨t, ht⟩
      rcases ht with ⟨n, rfl⟩
      exact ⟨(n, x), rfl⟩

/-- The native Ore quotient identifies exactly the displayed Day relation. -/
theorem ofPair_eq_iff (a b : ℕ × B) :
    ofPair s hs a = ofPair s hs b ↔ DayRel s a b := by
  let := centralPowersOreSet s hs
  rw [ofPair, ofPair, OreLocalization.oreDiv_eq_iff]
  constructor
  · rintro ⟨t, v, hnum, hden⟩
    rcases t with ⟨t, ht⟩
    rcases ht with ⟨m, rfl⟩
    simp only [Submonoid.smul_def, smul_eq_mul, powerDenominator_coe] at hnum hden
    refine ⟨m, ?_⟩
    calc
      s ^ m * (s ^ b.1 * a.2) = (s ^ m * s ^ b.1) * a.2 := by rw [mul_assoc]
      _ = (v * s ^ a.1) * a.2 := by rw [hden]
      _ = (s ^ a.1 * v) * a.2 := by rw [((hs v).pow_left a.1).eq]
      _ = s ^ a.1 * (s ^ m * b.2) := by rw [mul_assoc, ← hnum]
      _ = s ^ m * (s ^ a.1 * b.2) := by rw [← mul_assoc, ← pow_add,
        Nat.add_comm a.1 m, pow_add, mul_assoc]
  · rintro ⟨m, hm⟩
    refine ⟨powerDenominator s (m + a.1), s ^ (m + b.1), ?_, ?_⟩
    · simpa only [Submonoid.smul_def, smul_eq_mul, powerDenominator_coe,
        pow_add, mul_assoc] using hm.symm
    · simp only [powerDenominator_coe, ← pow_add]
      congr 1
      ac_rfl

/-- The displayed Day quotient maps to the native Ore quotient. -/
def quotientMap : Quotient (daySetoid s) → RingLocalization s hs :=
  Quotient.lift (ofPair s hs) (fun _ _ h => (ofPair_eq_iff s hs _ _).mpr h)

@[simp] theorem quotientMap_mk (a : ℕ × B) :
    quotientMap s hs (Quotient.mk (daySetoid s) a) = ofPair s hs a := rfl

theorem quotientMap_injective : Function.Injective (quotientMap s hs) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b h
  apply Quotient.sound
  exact (ofPair_eq_iff s hs a b).mp h

theorem quotientMap_surjective : Function.Surjective (quotientMap s hs) := by
  intro z
  obtain ⟨a, rfl⟩ := ofPair_surjective s hs z
  exact ⟨Quotient.mk (daySetoid s) a, rfl⟩

/-- A literal equivalence identifies the requested quotient with Mathlib's
noncommutative ring localization. The inverse is noncomputable. -/
noncomputable def quotientEquiv : Quotient (daySetoid s) ≃ RingLocalization s hs :=
  Equiv.ofBijective (quotientMap s hs)
    ⟨quotientMap_injective s hs, quotientMap_surjective s hs⟩

@[simp] theorem quotientEquiv_mk (a : ℕ × B) :
    quotientEquiv s hs (Quotient.mk (daySetoid s) a) = ofPair s hs a := rfl

/-- The degree-zero map is Mathlib's canonical numerator ring homomorphism. -/
def degreeZero : B →+* RingLocalization s hs := by
  letI := centralPowersOreSet s hs
  exact OreLocalization.numeratorRingHom

@[simp] theorem degreeZero_apply (x : B) :
    degreeZero s hs x = ofPair s hs (0, x) := by
  let := centralPowersOreSet s hs
  change OreLocalization.numeratorHom x = _
  rw [OreLocalization.numeratorHom_apply]
  unfold ofPair
  congr 1
  apply Subtype.ext
  exact (pow_zero s).symm

@[simp] theorem ofPair_zero : ofPair s hs (0, 0) = 0 := by
  rw [← degreeZero_apply]
  exact map_zero (degreeZero s hs)

@[simp] theorem ofPair_one : ofPair s hs (0, 1) = 1 := by
  rw [← degreeZero_apply]
  exact map_one (degreeZero s hs)

theorem ofPair_add (a b : ℕ × B) :
    ofPair s hs (dayAdd s a b) = ofPair s hs a + ofPair s hs b := by
  let := centralPowersOreSet s hs
  symm
  rw [ofPair, ofPair, OreLocalization.oreDiv_add_char
    (powerDenominator s a.1) (powerDenominator s b.1) (s ^ a.1)
    (powerDenominator s b.1)]
  · simp only [Submonoid.smul_def, smul_eq_mul, powerDenominator_coe,
      powerDenominator_mul, ofPair, dayAdd, Nat.add_comm]
  · simp only [powerDenominator_coe, ← pow_add, Nat.add_comm]

theorem ofPair_mul (a b : ℕ × B) :
    ofPair s hs (dayMul a b) = ofPair s hs a * ofPair s hs b := by
  let := centralPowersOreSet s hs
  symm
  rw [ofPair, ofPair, OreLocalization.oreDiv_mul_char a.2 b.2
    (powerDenominator s a.1) (powerDenominator s b.1) a.2
    (powerDenominator s b.1) ((hs a.2).pow_left b.1).eq]
  simp only [powerDenominator_mul, ofPair, dayMul, Nat.add_comm]

include hs in
theorem dayAdd_congr {a a' b b' : ℕ × B}
    (ha : DayRel s a a') (hb : DayRel s b b') :
    DayRel s (dayAdd s a b) (dayAdd s a' b') := by
  apply (ofPair_eq_iff s hs _ _).mp
  rw [ofPair_add, ofPair_add, (ofPair_eq_iff s hs _ _).mpr ha,
    (ofPair_eq_iff s hs _ _).mpr hb]

include hs in
theorem dayMul_congr {a a' b b' : ℕ × B}
    (ha : DayRel s a a') (hb : DayRel s b b') :
    DayRel s (dayMul a b) (dayMul a' b') := by
  apply (ofPair_eq_iff s hs _ _).mp
  rw [ofPair_mul, ofPair_mul, (ofPair_eq_iff s hs _ _).mpr ha,
    (ofPair_eq_iff s hs _ _).mpr hb]

theorem ofPair_zero_injective
    (hreg : Function.Injective (fun x : B => s * x)) :
    Function.Injective (fun x : B => ofPair s hs (0, x)) := by
  intro x y h
  exact (dayRel_zero_iff hreg x y).mp ((ofPair_eq_iff s hs _ _).mp h)

theorem degreeZero_injective
    (hreg : Function.Injective (fun x : B => s * x)) :
    Function.Injective (degreeZero s hs) := by
  intro x y h
  apply ofPair_zero_injective s hs hreg
  simpa only [degreeZero_apply] using h

section Star

variable [StarRing B] (hself : star s = s)

include hs hself in
theorem dayStar_congr {a b : ℕ × B} (h : DayRel s a b) :
    DayRel s (dayStar a) (dayStar b) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have hcomm (n : ℕ) (x : B) : x * s ^ n = s ^ n * x := ((hs x).pow_left n).eq.symm
  simpa only [dayStar, star_mul, star_pow, hself, hcomm] using congrArg star hm

include hself in
private theorem oreStar_wellDefined {x y : B} {t u : Submonoid.powers s}
    (h : (@OreLocalization.oreDiv B inferInstance (Submonoid.powers s)
      (centralPowersOreSet s hs) B inferInstance x t) =
      (@OreLocalization.oreDiv B inferInstance (Submonoid.powers s)
        (centralPowersOreSet s hs) B inferInstance y u)) :
    (@OreLocalization.oreDiv B inferInstance (Submonoid.powers s)
      (centralPowersOreSet s hs) B inferInstance (star x) t) =
      (@OreLocalization.oreDiv B inferInstance (Submonoid.powers s)
        (centralPowersOreSet s hs) B inferInstance (star y) u) := by
  let := centralPowersOreSet s hs
  rcases t with ⟨t, ht⟩
  rcases u with ⟨u, hu⟩
  rcases ht with ⟨k, rfl⟩
  rcases hu with ⟨l, rfl⟩
  change ofPair s hs (k, star x) = ofPair s hs (l, star y)
  exact (ofPair_eq_iff s hs _ _).mpr
    (dayStar_congr s hs hself ((ofPair_eq_iff s hs (k, x) (l, y)).mp h))

/-- The star operation is descended on the actual Ore quotient. -/
def starMap : RingLocalization s hs → RingLocalization s hs := by
  letI := centralPowersOreSet s hs
  exact Quotient.lift
    (fun p : B × Submonoid.powers s => OreLocalization.oreDiv (star p.1) p.2)
    (fun _ _ h => oreStar_wellDefined s hs hself (Quotient.sound h))

theorem starMap_ofPair (a : ℕ × B) :
    starMap s hs hself (ofPair s hs a) = ofPair s hs (dayStar a) := rfl

theorem starMap_involutive : Function.Involutive (starMap s hs hself) := by
  intro x
  obtain ⟨a, rfl⟩ := ofPair_surjective s hs x
  rw [starMap_ofPair, starMap_ofPair]
  simp only [dayStar, star_star]

theorem starMap_mul (x y : RingLocalization s hs) :
    starMap s hs hself (x * y) = starMap s hs hself y * starMap s hs hself x := by
  obtain ⟨a, rfl⟩ := ofPair_surjective s hs x
  obtain ⟨b, rfl⟩ := ofPair_surjective s hs y
  rw [← ofPair_mul, starMap_ofPair, starMap_ofPair, starMap_ofPair, ← ofPair_mul]
  simp only [dayStar, dayMul, star_mul, Nat.add_comm]

theorem starMap_add (x y : RingLocalization s hs) :
    starMap s hs hself (x + y) = starMap s hs hself x + starMap s hs hself y := by
  obtain ⟨a, rfl⟩ := ofPair_surjective s hs x
  obtain ⟨b, rfl⟩ := ofPair_surjective s hs y
  rw [← ofPair_add, starMap_ofPair, starMap_ofPair, starMap_ofPair, ← ofPair_add]
  have hcomm (n : ℕ) (z : B) : z * s ^ n = s ^ n * z := ((hs z).pow_left n).eq.symm
  simp only [dayStar, dayAdd, star_add, star_mul, star_pow, hself, hcomm]

/-- A star-ring structure on Mathlib's native ring localization. -/
@[instance_reducible]
def localizationStarRing : StarRing (RingLocalization s hs) where
  star := starMap s hs hself
  star_involutive := starMap_involutive s hs hself
  star_mul := starMap_mul s hs hself
  star_add := starMap_add s hs hself

theorem degreeZero_star (x : B) :
    letI := localizationStarRing s hs hself
    star (degreeZero s hs x) = degreeZero s hs (star x) := rfl

end Star
end Central

/-- With a regular denominator, raw multiplication is a congruence on the
whole coefficient ring exactly when that denominator is central. Applying
this to a coefficient subring gives the precise maximality statement. -/
theorem dayMul_congr_iff {s : B}
    (hreg : Function.Injective (fun x : B => s * x)) :
    (∀ a a' b b' : ℕ × B, DayRel s a a' → DayRel s b b' →
      DayRel s (dayMul a b) (dayMul a' b')) ↔ ∀ x : B, Commute s x := by
  constructor
  · intro h x
    apply (dayMul_identity_shift_iff hreg x).mp
    exact h (0, x) (0, x) (0, 1) (1, s) (dayRel_refl s _) (dayRel_one_shift s)
  · intro hs a a' b b' ha hb
    exact dayMul_congr s hs ha hb

end InfoGeometry.OperatorAlgebra.CentralPowerLocalization
