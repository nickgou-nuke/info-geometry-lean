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
