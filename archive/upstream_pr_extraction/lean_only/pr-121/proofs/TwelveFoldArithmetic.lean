import proofs.TwelveFoldSpectralBridge
import proofs.TwelveFoldCharacteristicPolynomial
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Exponent
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.GroupTheory.SpecificGroups.KleinFour


/-!
# Arithmetic divisor lattice of the certified twelvefold operator

The operator `masterTwelve` is the native matrix realization of a generator
of exact order twelve.  This file derives the exact orders of its divisor
powers constructively from the order theorem, rather than treating matrix
power identities as order claims.
-/

noncomputable section
namespace TwelveFoldArithmetic

open TwelveFoldSheetColorOmega TwelveFoldSpectralBridge
open TwoSheetThreeColorWeyl

abbrev W : M6C := masterTwelve
def T : M6C := W ^ 2
def OmegaChi : M6C := W ^ 3
def Gamma : M6C := W ^ 6
def X : M6C := W ^ 8

theorem W_pow_two : W ^ 2 = T := rfl
theorem W_pow_three : W ^ 3 = OmegaChi := rfl
theorem W_pow_six : W ^ 6 = Gamma := rfl
theorem W_pow_eight : W ^ 8 = X := rfl

theorem W_order : orderOf W = 12 := masterTwelve_orderOf

theorem W_pow_twelve : W ^ 12 = (1 : M6C) := masterTwelve_twelve

/-- A power of `W` is the identity exactly when its exponent is divisible by `12`. -/
theorem W_pow_eq_one_iff (n : ℕ) : W ^ n = (1 : M6C) ↔ 12 ∣ n := by
  rw [← orderOf_dvd_iff_pow_eq_one, W_order]

/-- No smaller positive power of `W` is the identity. -/
theorem W_pow_ne_one_of_lt {n : ℕ} (hn : 0 < n) (h : n < 12) :
    W ^ n ≠ (1 : M6C) := by
  intro hw
  have hdiv : 12 ∣ n := (W_pow_eq_one_iff n).mp hw
  exact (Nat.not_lt_of_ge (Nat.le_of_dvd hn hdiv)) h

/-! The scalar primitive sector of order twelve. -/
theorem primitive_exponent_iff {k : ℕ} (hk : k < 12) :
    Nat.Coprime k 12 ↔ k = 1 ∨ k = 5 ∨ k = 7 ∨ k = 11 := by
  interval_cases k <;> norm_num

theorem primitive_exponents_square_mod_twelve {k : ℕ}
    (hk : k < 12) (hc : Nat.Coprime k 12) : k * k % 12 = 1 := by
  have hk' := (primitive_exponent_iff hk).mp hc
  rcases hk' with rfl | rfl | rfl | rfl <;> norm_num

theorem W_pow_eight_ne_one : W ^ 8 ≠ (1 : M6C) := by
  rw [masterTwelve_eight]
  exact colorShiftSix_ne_one

theorem T_pow_six : T ^ 6 = (1 : M6C) := by
  rw [T, ← pow_mul, show 2 * 6 = 12 by norm_num, W_pow_twelve]

theorem T_pow_three : T ^ 3 = Gamma := by
  rw [T, ← pow_mul, show 2 * 3 = 6 by norm_num]
  rfl

theorem T_pow_three_ne_one : T ^ 3 ≠ (1 : M6C) := by
  rw [T_pow_three]
  change W ^ 6 ≠ (1 : M6C)
  exact TwelveFoldSpectralBridge.masterTwelve_six_ne_one

theorem T_pow_two_ne_one : T ^ 2 ≠ (1 : M6C) := by
  rw [T, ← pow_mul, show 2 * 2 = 4 by norm_num]
  exact TwelveFoldSpectralBridge.masterTwelve_four_ne_one

theorem T_order : orderOf T = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) T_pow_six
  intro p hp hpdvd
  have hp_le : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpdvd
  interval_cases p
  all_goals try norm_num at hp
  all_goals try norm_num at hpdvd
  · exact T_pow_three_ne_one
  · exact T_pow_two_ne_one

theorem OmegaChi_pow_four : OmegaChi ^ 4 = (1 : M6C) := by
  rw [OmegaChi, ← pow_mul, show 3 * 4 = 12 by norm_num, W_pow_twelve]

theorem OmegaChi_pow_two : OmegaChi ^ 2 = Gamma := by
  rw [OmegaChi, ← pow_mul, show 3 * 2 = 6 by norm_num]
  rfl

theorem OmegaChi_pow_two_ne_one : OmegaChi ^ 2 ≠ (1 : M6C) := by
  rw [OmegaChi_pow_two]
  change W ^ 6 ≠ (1 : M6C)
  exact TwelveFoldSpectralBridge.masterTwelve_six_ne_one

theorem OmegaChi_order : orderOf OmegaChi = 4 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) OmegaChi_pow_four
  intro p hp hpdvd
  have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hpdvd
  interval_cases p
  all_goals try norm_num at hp
  all_goals try norm_num at hpdvd
  exact OmegaChi_pow_two_ne_one

theorem Gamma_pow_two : Gamma ^ 2 = (1 : M6C) := by
  rw [Gamma, ← pow_mul, show 6 * 2 = 12 by norm_num, W_pow_twelve]

theorem Gamma_ne_one : Gamma ≠ (1 : M6C) := by
  change W ^ 6 ≠ (1 : M6C)
  exact TwelveFoldSpectralBridge.masterTwelve_six_ne_one

theorem Gamma_order : orderOf Gamma = 2 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) Gamma_pow_two
  intro p hp hpdvd
  have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpdvd
  interval_cases p
  all_goals try norm_num at hp
  all_goals try norm_num at hpdvd
  simpa using Gamma_ne_one

theorem X_pow_three : X ^ 3 = (1 : M6C) := by
  rw [X, ← pow_mul, show 8 * 3 = 24 by norm_num]
  rw [show 24 = 12 * 2 by norm_num, pow_mul, W_pow_twelve]
  simp

theorem X_ne_one : X ≠ (1 : M6C) := by
  rw [X]
  exact W_pow_eight_ne_one

theorem X_order : orderOf X = 3 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) X_pow_three
  intro p hp hpdvd
  have hp_le : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpdvd
  interval_cases p
  all_goals try norm_num at hp
  all_goals try norm_num at hpdvd
  simpa using X_ne_one

theorem common_order_two : T ^ 3 = Gamma ∧ OmegaChi ^ 2 = Gamma :=
  ⟨T_pow_three, OmegaChi_pow_two⟩

theorem twelvefold_divisor_orders :
    orderOf W = 12 ∧ orderOf T = 6 ∧ orderOf OmegaChi = 4 ∧
      orderOf Gamma = 2 ∧ orderOf X = 3 :=
  ⟨W_order, T_order, OmegaChi_order, Gamma_order, X_order⟩

/-- The arithmetic shadow of the cyclotomic Galois group: the unit group of
`ZMod 12` has four elements and exponent two. -/
theorem zmod12_units_card : Fintype.card (Units (ZMod 12)) = 4 := by
  decide

theorem zmod12_units_sq_one (u : Units (ZMod 12)) : u ^ 2 = 1 := by
  fin_cases u <;> decide

theorem zmod12_units_order_dvd_two (u : Units (ZMod 12)) : orderOf u ∣ 2 := by
  rw [orderOf_dvd_iff_pow_eq_one]
  exact zmod12_units_sq_one u

theorem zmod12_units_v4_shadow :
    Fintype.card (Units (ZMod 12)) = 4 ∧ ∀ u : Units (ZMod 12), u ^ 2 = 1 :=
  ⟨zmod12_units_card, zmod12_units_sq_one⟩

/-- The unit group of `ZMod 12` has exponent two. -/
theorem zmod12_units_exponent_two : Monoid.exponent (ZMod 12)ˣ = 2 := by
  have hpow : ∀ u : (ZMod 12)ˣ, u ^ 2 = 1 := zmod12_units_sq_one
  have hdiv : Monoid.exponent (ZMod 12)ˣ ∣ 2 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
  have hle : Monoid.exponent (ZMod 12)ˣ ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hne1 : Monoid.exponent (ZMod 12)ˣ ≠ 1 := by
    intro h1
    let u5 : (ZMod 12)ˣ := Units.mkOfMulEqOne (5 : ZMod 12) 5 (by decide)
    have hu5 : u5 ≠ 1 := by
      intro hu
      have h : (5 : ZMod 12) = 1 := by
        simpa [u5] using congrArg Units.val hu
      exact (by decide : (5 : ZMod 12) ≠ 1) h
    exact hu5 (by simpa [h1, u5] using Monoid.pow_exponent_eq_one u5)
  have hpos : 0 < Monoid.exponent (ZMod 12)ˣ := by
    have hexists : Monoid.ExponentExists (ZMod 12)ˣ := ⟨2, by decide, hpow⟩
    exact Monoid.exponent_pos.mpr hexists
  have hexp : Monoid.exponent (ZMod 12)ˣ = 2 := by
    omega
  exact hexp

/-- The fourth cyclotomic polynomial in explicit native form. -/
theorem cyclotomic_four_explicit :
    Polynomial.cyclotomic 4 ℚ = Polynomial.X ^ 2 + 1 := by
  have hpd : Nat.properDivisors 4 = ({1, 2} : Finset ℕ) := by
    native_decide
  have hmonic : ((Polynomial.X - 1) * (Polynomial.X + 1) : Polynomial ℚ).Monic := by
    simpa using (Polynomial.monic_X_sub_C (1 : ℚ)).mul (Polynomial.monic_X_add_C 1)
  have hdeg :
      (0 : Polynomial ℚ).degree <
        ((Polynomial.X - 1) * (Polynomial.X + 1) : Polynomial ℚ).degree := by
    have h1 : (Polynomial.X - (1 : Polynomial ℚ)).degree = 1 := by
      simpa using (Polynomial.degree_X_sub_C (1 : ℚ))
    have h2 : (Polynomial.X + (1 : Polynomial ℚ)).degree = 1 := by
      simpa using (Polynomial.degree_X_add_C (1 : ℚ))
    rw [Polynomial.degree_mul, h1, h2]
    decide
  have hdiv := Polynomial.div_modByMonic_unique
    (f := (Polynomial.X ^ 4 - 1 : Polynomial ℚ))
    (g := (Polynomial.X - 1) * (Polynomial.X + 1))
    (q := Polynomial.X ^ 2 + 1)
    (r := 0)
    hmonic
    ⟨by ring, hdeg⟩
  rw [Polynomial.cyclotomic_eq_X_pow_sub_one_div (n := 4) (R := ℚ) (by decide)]
  simpa [hpd, Polynomial.cyclotomic_one, Polynomial.cyclotomic_two] using hdiv.left

/-- The twelfth cyclotomic polynomial in explicit native form. -/
theorem cyclotomic_twelve_explicit :
    Polynomial.cyclotomic 12 ℚ = Polynomial.X ^ 4 - Polynomial.X ^ 2 + 1 := by
  have h4 : Polynomial.cyclotomic 4 ℚ = Polynomial.X ^ 2 + 1 :=
    cyclotomic_four_explicit
  have hpd : Nat.properDivisors 12 = ({1, 2, 3, 4, 6} : Finset ℕ) := by
    native_decide
  have hmonic :
      ((Polynomial.X - 1) * (Polynomial.X + 1) *
        (Polynomial.X ^ 2 + Polynomial.X + 1) *
        (Polynomial.X ^ 2 + 1) *
        (Polynomial.X ^ 2 - Polynomial.X + 1) : Polynomial ℚ).Monic := by
    have h1 : (Polynomial.X - (1 : Polynomial ℚ)).Monic := by
      simpa using (Polynomial.cyclotomic.monic 1 ℚ)
    have h2 : (Polynomial.X + (1 : Polynomial ℚ)).Monic := by
      simpa using (Polynomial.cyclotomic.monic 2 ℚ)
    have h3 : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℚ).Monic := by
      simpa [Polynomial.cyclotomic_three] using (Polynomial.cyclotomic.monic 3 ℚ)
    have h4m : (Polynomial.X ^ 2 + 1 : Polynomial ℚ).Monic := by
      simpa [h4] using (Polynomial.cyclotomic.monic 4 ℚ)
    have h6 : (Polynomial.X ^ 2 - Polynomial.X + 1 : Polynomial ℚ).Monic := by
      simpa [Polynomial.cyclotomic_six] using (Polynomial.cyclotomic.monic 6 ℚ)
    simpa [mul_assoc] using h1.mul (h2.mul (h3.mul (h4m.mul h6)))
  have hdeg :
      (0 : Polynomial ℚ).degree <
        ((Polynomial.X - 1) * (Polynomial.X + 1) *
          (Polynomial.X ^ 2 + Polynomial.X + 1) *
          (Polynomial.X ^ 2 + 1) *
          (Polynomial.X ^ 2 - Polynomial.X + 1) : Polynomial ℚ).degree := by
    have hdeg1 : (Polynomial.X - (1 : Polynomial ℚ)).degree = 1 := by
      simpa using (Polynomial.degree_X_sub_C (1 : ℚ))
    have hdeg2 : (Polynomial.X + (1 : Polynomial ℚ)).degree = 1 := by
      simpa using (Polynomial.degree_X_add_C (1 : ℚ))
    have hdeg3 : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℚ).degree = 2 := by
      simpa [Polynomial.cyclotomic_three] using (Polynomial.degree_cyclotomic 3 ℚ)
    have hdeg4 : (Polynomial.X ^ 2 + 1 : Polynomial ℚ).degree = 2 := by
      simpa [h4] using (Polynomial.degree_cyclotomic 4 ℚ)
    have hdeg6 : (Polynomial.X ^ 2 - Polynomial.X + 1 : Polynomial ℚ).degree = 2 := by
      simpa [Polynomial.cyclotomic_six] using (Polynomial.degree_cyclotomic 6 ℚ)
    norm_num [mul_assoc, Polynomial.degree_mul, hdeg1, hdeg2, hdeg3, hdeg4, hdeg6]
    exact bot_lt_iff_ne_bot.mpr (by simp)
  have hdiv := Polynomial.div_modByMonic_unique
    (f := (Polynomial.X ^ 12 - 1 : Polynomial ℚ))
    (g := (Polynomial.X - 1) * (Polynomial.X + 1) *
        (Polynomial.X ^ 2 + Polynomial.X + 1) *
        (Polynomial.X ^ 2 + 1) *
        (Polynomial.X ^ 2 - Polynomial.X + 1))
    (q := Polynomial.X ^ 4 - Polynomial.X ^ 2 + 1)
    (r := 0)
    hmonic
    ⟨by ring, hdeg⟩
  rw [Polynomial.cyclotomic_eq_X_pow_sub_one_div (n := 12) (R := ℚ) (by decide)]
  simpa [hpd, Polynomial.cyclotomic_one, Polynomial.cyclotomic_two,
    Polynomial.cyclotomic_three, Polynomial.cyclotomic_six, h4, mul_assoc]
    using hdiv.left

/-- The full factorization of `X^12 - 1` into the six cyclotomic sectors. -/
theorem X12_sub_one_factorization :
    (Polynomial.X ^ 12 - 1 : Polynomial ℚ) =
      Polynomial.cyclotomic 1 ℚ * Polynomial.cyclotomic 2 ℚ *
        Polynomial.cyclotomic 3 ℚ * Polynomial.cyclotomic 4 ℚ *
        Polynomial.cyclotomic 6 ℚ * Polynomial.cyclotomic 12 ℚ := by
  have hdivs : (12).divisors = ({1, 2, 3, 4, 6, 12} : Finset ℕ) := by
    native_decide
  simpa [hdivs, Polynomial.cyclotomic_one, Polynomial.cyclotomic_two,
    Polynomial.cyclotomic_three, Polynomial.cyclotomic_six,
    cyclotomic_four_explicit, mul_assoc,
    mul_comm, mul_left_comm] using
    (Polynomial.prod_cyclotomic_eq_X_pow_sub_one (n := 12) (R := ℚ) (by decide)).symm

/-- Primitive twelfth roots are exactly the roots of `Φ₁₂`. -/
theorem primitive_twelve_root_iff {ζ : ℂ} :
    (Polynomial.cyclotomic 12 ℂ).IsRoot ζ ↔ IsPrimitiveRoot ζ 12 := by
  simpa using (Polynomial.isRoot_cyclotomic_iff (R := ℂ) (n := 12) (μ := ζ))

/-- Every primitive twelfth root is a root of `Φ₁₂`. -/
theorem primitive_twelve_root {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 12) :
    (Polynomial.cyclotomic 12 ℂ).IsRoot ζ :=
  IsPrimitiveRoot.isRoot_cyclotomic (R := ℂ) (n := 12) (by decide) hζ

/-- The cyclotomic Galois group of the twelfth cyclotomic field is the unit
group of `ZMod 12`. -/
noncomputable def cyclotomic12_galEquivUnits :
    Gal(CyclotomicField 12 ℚ / ℚ) ≃* (ZMod 12)ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod (n := 12) (K := CyclotomicField 12 ℚ)

theorem cyclotomic12_galEquivUnits_nonempty :
    Nonempty (Gal(CyclotomicField 12 ℚ / ℚ) ≃* (ZMod 12)ˣ) := by
  exact ⟨cyclotomic12_galEquivUnits⟩

/-- The Galois group of `Q(ζ₁₂)` has four elements. -/
theorem cyclotomic12_gal_card :
    Nat.card (Gal(CyclotomicField 12 ℚ / ℚ)) = 4 := by
  simpa [Nat.card_eq_fintype_card] using
    (Fintype.card_congr cyclotomic12_galEquivUnits.toEquiv).trans zmod12_units_card

/-- The Galois group of `Q(ζ₁₂)` has exponent two. -/
theorem cyclotomic12_gal_exponent :
    Monoid.exponent (Gal(CyclotomicField 12 ℚ / ℚ)) = 2 := by
  rw [Monoid.exponent_eq_of_mulEquiv cyclotomic12_galEquivUnits]
  simpa using zmod12_units_exponent_two

/-- The Galois group of `Q(ζ₁₂)` is itself a Klein four group. -/
theorem cyclotomic12_galIsKleinFour :
    IsKleinFour (Gal(CyclotomicField 12 ℚ / ℚ)) := by
  exact IsKleinFour.mk cyclotomic12_gal_card cyclotomic12_gal_exponent

/-- The unit group of `ZMod 12` is a Klein four group. -/
theorem zmod12_units_isKleinFour : IsKleinFour (ZMod 12)ˣ := by
  refine IsKleinFour.mk ?card ?exp
  · simpa using (zmod12_units_card)
  · exact zmod12_units_exponent_two

/-- The cyclotomic Galois group of `Q(ζ₁₂)` is a Klein four group. -/
theorem cyclotomic12_galEquivV4 :
    Nonempty (Gal(CyclotomicField 12 ℚ / ℚ) ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
  letI : IsKleinFour (Gal(CyclotomicField 12 ℚ / ℚ)) := cyclotomic12_galIsKleinFour
  exact IsKleinFour.nonempty_mulEquiv (G₁ := Gal(CyclotomicField 12 ℚ / ℚ))
    (G₂ := Multiplicative (ZMod 2 × ZMod 2))

/-- The Galois group of `Q(ζ₁₂)` has four elements. -/
theorem cyclotomic12_gal_fintype_card :
    Fintype.card (Gal(CyclotomicField 12 ℚ / ℚ)) = 4 := by
  simpa [Nat.card_eq_fintype_card] using cyclotomic12_gal_card

/-- Every unit in `(ZMod 12)ˣ` is an involution. -/
theorem zmod12_units_inv_eq_self (u : (ZMod 12)ˣ) : u⁻¹ = u := by
  exact inv_eq_self_of_exponent_two zmod12_units_exponent_two u

/-- Every Galois automorphism of `Q(ζ₁₂)` is an involution. -/
theorem cyclotomic12_gal_inv_eq_self (σ : Gal(CyclotomicField 12 ℚ / ℚ)) : σ⁻¹ = σ := by
  exact inv_eq_self_of_exponent_two cyclotomic12_gal_exponent σ

/-- Complex conjugation inverts any root of unity. -/
theorem complex_conj_rootsOfUnity_inversion {ζ : ℂˣ} {n : ℕ} [NeZero n]
    (hζ : ζ ∈ rootsOfUnity n ℂ) :
    (starRingEnd ℂ) ζ = ζ⁻¹ := by
  simpa using (Complex.conj_rootsOfUnity (ζ := ζ) (n := n) hζ)

/-- The twelfth root-of-unity inversion law, specialized to `n = 12`. -/
theorem complex_conj_rootsOfUnity_inversion12 {ζ : ℂˣ}
    (hζ : ζ ∈ rootsOfUnity 12 ℂ) :
    (starRingEnd ℂ) ζ = ζ⁻¹ := by
  simpa using (complex_conj_rootsOfUnity_inversion (ζ := ζ) (n := 12) hζ)

/-- Primitive twelfth roots are inverted by complex conjugation. -/
theorem complex_conj_primitive_root_inversion12 {ζ : ℂˣ} (hζ : IsPrimitiveRoot ζ 12) :
    (starRingEnd ℂ) ζ = ζ⁻¹ := by
  exact complex_conj_rootsOfUnity_inversion12 hζ.mem_rootsOfUnity

/-- Every element in the `ZMod 12` unit group squares to one. -/
theorem zmod12_units_mul_self_eq_one (u : (ZMod 12)ˣ) : u * u = (1 : (ZMod 12)ˣ) := by
  simpa [zmod12_units_inv_eq_self u] using (mul_inv_cancel u)

/-- The square of every element in the Galois group `Gal(ℚ(ζ₁₂)/ℚ)` is the identity. -/
theorem cyclotomic12_gal_mul_self_eq_one (σ : Gal(CyclotomicField 12 ℚ / ℚ)) :
    σ * σ = (1 : Gal(CyclotomicField 12 ℚ / ℚ)) := by
  simpa [cyclotomic12_gal_inv_eq_self σ] using (mul_inv_cancel σ)

/-- Order of every element in `Gal(ℚ(ζ₁₂)/ℚ)` divides two. -/
theorem cyclotomic12_gal_order_dvd_two (σ : Gal(CyclotomicField 12 ℚ / ℚ)) :
    orderOf σ ∣ 2 := by
  rw [orderOf_dvd_iff_pow_eq_one]
  simpa [pow_two] using (cyclotomic12_gal_mul_self_eq_one σ)

/-- The certified matrix spectrum of the master twelvefold operator. -/
theorem masterTwelve_charpoly_spectrum :
    ∀ (ω : ℂ), ω ^ 2 + ω + 1 = 0 →
    TwelveFoldSheetColorOmega.masterTwelve.charpoly =
      (Polynomial.X ^ 3 - 1) * (Polynomial.X ^ 3 - Polynomial.C Complex.I) := by
  intro ω hω
  simpa using
    (TwelveFoldCharacteristicPolynomial.masterTwelve_charpoly (ω := ω) (hω := hω))

/-- The certified characteristic polynomial of the master twelvefold operator. -/
theorem masterTwelve_charpoly_closed :
    TwelveFoldSheetColorOmega.masterTwelve.charpoly =
      (Polynomial.X ^ 3 - 1) * (Polynomial.X ^ 3 - Polynomial.C Complex.I) := by
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hωprim : IsPrimitiveRoot ω 3 := by
    simpa [ω] using (Complex.isPrimitiveRoot_exp 3 (by decide))
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have hroot := IsPrimitiveRoot.isRoot_cyclotomic (R := ℂ) (n := 3) (by decide) hωprim
    simpa [ω, Polynomial.cyclotomic_three] using hroot
  simpa [ω] using
    (TwelveFoldCharacteristicPolynomial.masterTwelve_charpoly (ω := ω) (hω := hω))

/-! ## Generalized Pauli basis on six states -/

/-- A concrete primitive cubic root used by the finite colour clock. -/
def ω3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem omega3_root : ω3 ^ 2 + ω3 + 1 = 0 := by
  have hωprim : IsPrimitiveRoot ω3 3 := by
    simpa [ω3] using (Complex.isPrimitiveRoot_exp 3 (by decide))
  have hroot := IsPrimitiveRoot.isRoot_cyclotomic (R := ℂ) (n := 3) (by decide) hωprim
  simpa [Polynomial.cyclotomic_three, ω3] using hroot

/-- Primitive sixth root and its square. -/
def ζ6 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 6)

theorem zeta6_sq : ζ6 ^ 2 = ω3 := by
  have hnat := Complex.exp_nat_mul (2 * Real.pi * Complex.I / 6) (2 : ℕ)
  have hred : (2 : ℂ) * (2 * Real.pi * Complex.I / (6 : ℂ)) =
      2 * Real.pi * Complex.I / (3 : ℂ) := by
    norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    ζ6 ^ 2 = Complex.exp (2 * Real.pi * Complex.I / (6 : ℂ)) ^ 2 := by
      rfl
    _ = Complex.exp (2 * (2 * Real.pi * Complex.I / (6 : ℂ))) := by
      simpa [pow_two] using hnat.symm
    _ = Complex.exp (2 * Real.pi * Complex.I / (3 : ℂ)) := by
      simpa [hred]
    _ = ω3 := by rfl

/-- Generalized Pauli generators on six states. -/
def X6 : M6C := tensor sheetFlip colorShift
def Z6 : M6C := tensor sheetGamma (colorClock ω3)

private theorem tensor_smul_left (a : ℂ) (A : M2C) (B : M3C) :
    tensor (a • A) B = a • tensor A B := by
  ext ⟨i, b⟩ ⟨j, c⟩
  simp [tensor, Matrix.kroneckerMap_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

private theorem tensor_smul_right (a : ℂ) (A : M2C) (B : M3C) :
    tensor A (a • B) = a • tensor A B := by
  ext ⟨i, b⟩ ⟨j, c⟩
  simp [tensor, Matrix.kroneckerMap_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

private theorem sheet_flip_comm : sheetGamma * sheetFlip = -(sheetFlip * sheetGamma) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sheetGamma, sheetFlip, sheetPlus, sheetMinus,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem X6_pow_six : X6 ^ 6 = (1 : M6C) := by
  have hflip2 : (sheetFlip : M2C) ^ 2 = (1 : M2C) := by
    simpa [pow_two] using sheet_parity.2.1
  have hshift3 : colorShift ^ 3 = (1 : M3C) := (color_weyl ω3 omega3_root).1
  have hflip6 : (sheetFlip : M2C) ^ 6 = (1 : M2C) := by
    calc
      (sheetFlip : M2C) ^ 6 = (sheetFlip : M2C) ^ (2 * 3) := by
        norm_num
      _ = (sheetFlip ^ 2) ^ 3 := by
        simpa [show (2 : ℕ) * (3 : ℕ) = 6 by norm_num] using (pow_mul (sheetFlip : M2C) 2 3)
      _ = (1 : M2C) ^ 3 := by rw [hflip2]
      _ = (1 : M2C) := by simp
  have hshift6 : colorShift ^ 6 = (1 : M3C) := by
    calc
      colorShift ^ 6 = colorShift ^ (3 * 2) := by norm_num
      _ = (colorShift ^ 3) ^ 2 := by
        simpa [show (3 : ℕ) * (2 : ℕ) = 6 by norm_num] using (pow_mul colorShift 3 2)
      _ = (1 : M3C) ^ 2 := by rw [hshift3]
      _ = (1 : M3C) := by simp
  calc
    X6 ^ 6 = tensor (sheetFlip ^ 6) (colorShift ^ 6) := by
      simp [X6, tensor_pow]
    _ = tensor (1 : M2C) (1 : M3C) := by rw [hflip6, hshift6]
    _ = (1 : M6C) := by simp [tensor_one]

theorem Z6_pow_six : Z6 ^ 6 = (1 : M6C) := by
  have hgamma2 : (sheetGamma : M2C) ^ 2 = (1 : M2C) := by
    simpa [pow_two] using sheet_parity.1
  have hclock3 : colorClock ω3 ^ 3 = (1 : M3C) := (color_weyl ω3 omega3_root).2.1
  have hgamma6 : (sheetGamma : M2C) ^ 6 = (1 : M2C) := by
    calc
      (sheetGamma : M2C) ^ 6 = (sheetGamma : M2C) ^ (2 * 3) := by norm_num
      _ = (sheetGamma ^ 2) ^ 3 := by
        simpa [show (2 : ℕ) * (3 : ℕ) = 6 by norm_num] using (pow_mul (sheetGamma : M2C) 2 3)
      _ = (1 : M2C) ^ 3 := by rw [hgamma2]
      _ = (1 : M2C) := by simp
  have hclock6 : colorClock ω3 ^ 6 = (1 : M3C) := by
    calc
      colorClock ω3 ^ 6 = colorClock ω3 ^ (3 * 2) := by norm_num
      _ = (colorClock ω3 ^ 3) ^ 2 := by
        simpa [show (3 : ℕ) * (2 : ℕ) = 6 by norm_num] using (pow_mul (colorClock ω3) 3 2)
      _ = (1 : M3C) ^ 2 := by rw [hclock3]
      _ = (1 : M3C) := by simp
  calc
    Z6 ^ 6 = tensor (sheetGamma ^ 6) (colorClock ω3 ^ 6) := by
      simp [Z6, tensor_pow]
    _ = tensor (1 : M2C) (1 : M3C) := by rw [hgamma6, hclock6]
    _ = (1 : M6C) := by simp [tensor_one]

theorem X6_Z6_comm :
    Z6 * X6 = (-(ω3 : ℂ)) • (X6 * Z6) := by
  have hcol : colorClock ω3 * colorShift = ω3 • (colorShift * colorClock ω3) :=
    (color_weyl ω3 omega3_root).2.2
  calc
    Z6 * X6 = tensor (sheetGamma * sheetFlip) ((colorClock ω3) * colorShift) := by
      simp [Z6, X6, tensor_mul]
    _ = tensor (-(sheetFlip * sheetGamma)) (ω3 • (colorShift * colorClock ω3)) := by
      rw [sheet_flip_comm, hcol]
    _ = (-1 : ℂ) • tensor (sheetFlip * sheetGamma) (ω3 • (colorShift * colorClock ω3)) := by
      simpa using (tensor_smul_left (-1 : ℂ) (sheetFlip * sheetGamma)
        (ω3 • (colorShift * colorClock ω3)))
    _ = (-ω3) • tensor (sheetFlip * sheetGamma) (colorShift * colorClock ω3) := by
      rw [tensor_smul_right]
      simp [smul_smul]
    _ = (-(ω3 : ℂ)) • (X6 * Z6) := by
      simp [X6, Z6, tensor_mul]

theorem X6_Z6_comm_with_zeta6 :
    Z6 * X6 = (-(ζ6 : ℂ) ^ 2) • (X6 * Z6) := by
  rw [zeta6_sq, X6_Z6_comm]


end TwelveFoldArithmetic
end noncomputable section
