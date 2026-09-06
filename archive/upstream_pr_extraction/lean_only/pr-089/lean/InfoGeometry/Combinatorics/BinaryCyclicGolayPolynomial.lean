import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

namespace InfoGeometry.Combinatorics.BinaryCyclicGolayPolynomial

abbrev F₂ := ZMod 2
abbrev R := Polynomial F₂

local notation "X" => Polynomial.X

noncomputable def generator : R :=
  1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 10 + X ^ 11

noncomputable def checkPolynomial : R :=
  1 + X + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9 + X ^ 11

noncomputable def parityCheckPolynomial : R :=
  (X + 1) * checkPolynomial

theorem generator_factorization :
    (X + 1) * generator * checkPolynomial = X ^ 23 + 1 := by
  simp only [generator, checkPolynomial]
  ring_nf
  have h2 : (2 : R) = 0 := by
    calc
      (2 : R) = Polynomial.C (2 : F₂) := (map_natCast Polynomial.C 2).symm
      _ = 0 := by rw [show (2 : F₂) = 0 by rfl, map_zero]
  have h4 : (4 : R) = 0 := by rw [show (4 : R) = 2 * 2 by norm_num, h2, zero_mul]
  have h6 : (6 : R) = 0 := by rw [show (6 : R) = 2 * 3 by norm_num, h2, zero_mul]
  have h10 : (10 : R) = 0 := by rw [show (10 : R) = 2 * 5 by norm_num, h2, zero_mul]
  simp [h2, h4, h6, h10]

theorem generator_dvd_x23_add_one :
    generator ∣ X ^ 23 + 1 := by
  refine ⟨(X + 1) * checkPolynomial, ?_⟩
  simpa [mul_assoc, mul_left_comm, mul_comm] using generator_factorization.symm

theorem checkPolynomial_dvd_x23_add_one :
    checkPolynomial ∣ X ^ 23 + 1 := by
  refine ⟨(X + 1) * generator, ?_⟩
  simpa [mul_assoc, mul_left_comm, mul_comm] using generator_factorization.symm

theorem generator_mul_parityCheckPolynomial :
    generator * parityCheckPolynomial = X ^ 23 + 1 := by
  unfold parityCheckPolynomial
  simpa [mul_assoc, mul_left_comm, mul_comm] using generator_factorization

theorem add_one_dvd_pow_add_one_of_odd
    {S : Type*} [CommRing S] (a : S) {n : ℕ} (hn : Odd n) :
    a + 1 ∣ a ^ n + 1 := by
  rcases hn with ⟨k, rfl⟩
  induction k with
  | zero =>
      exact ⟨1, by ring⟩
  | succ k ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨a ^ 2 * q - a + 1, ?_⟩
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega]
      rw [pow_add]
      calc
        a ^ (2 * k + 1) * a ^ 2 + 1 =
            a ^ 2 * (a ^ (2 * k + 1) + 1) - (a ^ 2 - 1) := by ring
        _ = a ^ 2 * ((a + 1) * q) - (a ^ 2 - 1) := by rw [hq]
        _ = (a + 1) * (a ^ 2 * q - a + 1) := by ring

def generatorCoefficientFormula (k : ℕ) : F₂ :=
  match k with
  | 0 | 2 | 4 | 5 | 6 | 10 | 11 => 1
  | _ => 0

theorem generator_coeff_of_lt (k : ℕ) (hk : k < 23) :
    generator.coeff k = generatorCoefficientFormula k := by
  have hk' : k ≤ 22 := by omega
  interval_cases k <;>
    simp [generator, generatorCoefficientFormula, Polynomial.coeff_one,
      Polynomial.coeff_X_pow]

end InfoGeometry.Combinatorics.BinaryCyclicGolayPolynomial

namespace InfoGeometry.Combinatorics.BinaryCyclicGolayPolynomial

theorem x_pow_add_one_dvd_x_pow_succ_sub_x (n : ℕ) :
    (Polynomial.X ^ n + 1 : Polynomial (ZMod 2)) ∣
      (Polynomial.X ^ (n + 1) - Polynomial.X : Polynomial (ZMod 2)) := by
  have hneg : -(Polynomial.X : Polynomial (ZMod 2)) = Polynomial.X := by
    apply (neg_eq_iff_add_eq_zero).2
    rw [← two_nsmul (Polynomial.X : Polynomial (ZMod 2))]
    rw [nsmul_eq_mul]
    have htwo : (↑(2 : ℕ) : Polynomial (ZMod 2)) = 0 :=
      CharP.cast_eq_zero (Polynomial (ZMod 2)) 2
    rw [htwo, zero_mul]
  refine ⟨Polynomial.X, ?_⟩
  calc
    Polynomial.X ^ (n + 1) - Polynomial.X =
        (Polynomial.X ^ n * Polynomial.X) - Polynomial.X := by
      rw [pow_succ]
    _ = (Polynomial.X ^ n + 1) * Polynomial.X := by
      rw [sub_eq_add_neg, hneg, add_mul, one_mul]

end InfoGeometry.Combinatorics.BinaryCyclicGolayPolynomial

namespace InfoGeometry.Combinatorics.BinaryCyclicGolayPolynomial

theorem x23_add_one_dvd_x23_mul_89_add_one :
    (Polynomial.X ^ 23 + 1 : Polynomial (ZMod 2)) ∣
      (Polynomial.X ^ (23 * 89) + 1 : Polynomial (ZMod 2)) := by
  rcases add_one_dvd_pow_add_one_of_odd (S := Polynomial (ZMod 2))
      ((Polynomial.X : Polynomial (ZMod 2)) ^ 23)
      (n := 89) (by exact ⟨44, by norm_num⟩) with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    Polynomial.X ^ (23 * 89) + 1 =
        ((Polynomial.X : Polynomial (ZMod 2)) ^ 23) ^ 89 + 1 := by
      simpa only [pow_mul]
    _ = ((Polynomial.X : Polynomial (ZMod 2)) ^ 23 + 1) * q := hq

end InfoGeometry.Combinatorics.BinaryCyclicGolayPolynomial

namespace InfoGeometry.Combinatorics.BinaryCyclicGolayPolynomial

theorem generator_dvd_x23_mul_89_add_one :
    generator ∣ (Polynomial.X ^ (23 * 89) + 1 : Polynomial F₂) := by
  rcases generator_dvd_x23_add_one with ⟨q₁, hq₁⟩
  rcases x23_add_one_dvd_x23_mul_89_add_one with ⟨q₂, hq₂⟩
  refine ⟨q₁ * q₂, ?_⟩
  rw [hq₂, hq₁]
  ring

end InfoGeometry.Combinatorics.BinaryCyclicGolayPolynomial
