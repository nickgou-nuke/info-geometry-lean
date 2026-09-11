import Mathlib.FieldTheory.Finite.Extension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.NormNum
import InfoGeometry.Combinatorics.BinaryBCHMinimumDistance
import InfoGeometry.Combinatorics.BinaryCyclicGolayPolynomial

/-!
# The finite field carrying a primitive 23rd root

The binary Golay polynomial has degree eleven.  This owner isolates the
finite-field group-theoretic fact needed for its root analysis: the units of
`𝔽₂¹¹` have order `2^11 - 1 = 23 * 89`, hence Cauchy's theorem supplies a unit
of order `23`.
-/

namespace InfoGeometry.Combinatorics.BinaryGolayRootField

abbrev RootField := FiniteField.Extension (ZMod 2) 2 11

noncomputable instance : Fintype RootField := Fintype.ofFinite RootField

theorem rootField_card : Fintype.card RootField = 2048 := by
  rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension]
  norm_num

theorem rootField_units_natCard : Nat.card RootFieldˣ = 2047 := by
  rw [Nat.card_units, FiniteField.natCard_extension]
  norm_num

theorem twentyThree_dvd_rootField_units_natCard : 23 ∣ Nat.card RootFieldˣ := by
  rw [rootField_units_natCard]
  norm_num

theorem exists_root_of_order_twentyThree :
    ∃ x : RootFieldˣ, orderOf x = 23 := by
  classical
  letI : Fintype RootFieldˣ := Fintype.ofFinite RootFieldˣ
  have hprime : Nat.Prime 23 := by decide
  letI : Fact (Nat.Prime 23) := ⟨hprime⟩
  exact exists_prime_orderOf_dvd_card 23 (by
    rw [← Nat.card_eq_fintype_card, rootField_units_natCard]
    norm_num)

theorem root_powers_injective (x : RootFieldˣ) (hx : orderOf x = 23) :
    Function.Injective (fun i : Fin 23 =>
      (x : RootField) ^ (i : ℕ)) := by
  intro i j hij
  have hunit : x ^ (i : ℕ) = x ^ (j : ℕ) := by
    apply Units.ext
    exact hij
  have hmod : (i : ℕ) ≡ (j : ℕ) [MOD orderOf x] :=
    (pow_eq_pow_iff_modEq.mp hunit)
  rw [hx] at hmod
  apply Fin.ext
  exact hmod.eq_of_lt_of_lt i.isLt j.isLt

theorem exists_root_with_injective_powers :
    ∃ α : RootField, Function.Injective (fun i : Fin 23 =>
      α ^ (i : ℕ)) := by
  rcases exists_root_of_order_twentyThree with ⟨x, hx⟩
  exact ⟨x, root_powers_injective x hx⟩

theorem root_twentyThree_power_eq_one (x : RootFieldˣ)
    (hx : orderOf x = 23) :
    (x : RootField) ^ 23 = 1 := by
  have horder : orderOf (x : RootField) = 23 := by
    simpa only [orderOf_units] using hx
  exact orderOf_dvd_iff_pow_eq_one.mp (by
    rw [horder]
    )

theorem root_is_generator_or_checkPolynomial (x : RootFieldˣ)
    (hx : orderOf x = 23) :
    Polynomial.eval₂
        (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) (x : RootField)
        BinaryCyclicGolayPolynomial.generator = 0 ∨
      Polynomial.eval₂
          (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) (x : RootField)
        BinaryCyclicGolayPolynomial.checkPolynomial = 0 := by
  have hfactor := congrArg
    (Polynomial.eval₂
      (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) (x : RootField))
    BinaryCyclicGolayPolynomial.generator_factorization
  have hzero : Polynomial.eval₂
      (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) (x : RootField)
      ((Polynomial.X + 1) * BinaryCyclicGolayPolynomial.generator *
        BinaryCyclicGolayPolynomial.checkPolynomial) = 0 := by
    have hchar : (1 : RootField) + 1 = 0 := by
      have hbase :
          (1 : BinaryCyclicGolayPolynomial.F₂) + 1 = 0 := by
        decide
      have hmap := congrArg
        (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) hbase
      simpa only [map_add, map_zero, map_one] using hmap
    rw [hfactor]
    simp [Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, hchar, root_twentyThree_power_eq_one x hx]
  have hprod :
      ((x : RootField) + 1) *
          Polynomial.eval₂
            (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) (x : RootField)
            BinaryCyclicGolayPolynomial.generator *
        Polynomial.eval₂
          (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) (x : RootField)
          BinaryCyclicGolayPolynomial.checkPolynomial = 0 := by
    simpa [Polynomial.eval₂_mul, Polynomial.eval₂_add,
      Polynomial.eval₂_X] using hzero
  rcases mul_eq_zero.mp hprod with hleft | hcheck
  · rcases mul_eq_zero.mp hleft with hfirst | hgenerator
    · have hneg : (x : RootField) = -1 :=
        eq_neg_of_add_eq_zero_left hfirst
      have horder : orderOf (x : RootField) ≤ 2 := by
        rw [hneg, orderOf_neg_one]
        split <;> omega
      have hxorder : orderOf (x : RootField) = 23 := by
        simpa only [orderOf_units] using hx
      omega
    · exact Or.inl hgenerator
  · exact Or.inr hcheck

theorem generator_dvd_rootField_card_sub_X :
    BinaryCyclicGolayPolynomial.generator ∣
      (Polynomial.X ^ Fintype.card RootField - Polynomial.X :
        Polynomial (ZMod 2)) := by
  have hcard : Fintype.card RootField = 23 * 89 + 1 := by
    norm_num [rootField_card]
  rw [hcard]
  rcases BinaryCyclicGolayPolynomial.generator_dvd_x23_mul_89_add_one with
    ⟨q₁, hq₁⟩
  rcases BinaryCyclicGolayPolynomial.x_pow_add_one_dvd_x_pow_succ_sub_x
      (23 * 89) with ⟨q₂, hq₂⟩
  refine ⟨q₁ * q₂, ?_⟩
  rw [hq₂, hq₁]
  ring

theorem mapped_generator_splits :
    (Polynomial.map
      (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField)
      BinaryCyclicGolayPolynomial.generator).Splits := by
  apply BinaryBCHMinimumDistance.mapped_polynomial_splits_of_dvd_card_sub_X
  exact generator_dvd_rootField_card_sub_X

theorem mapped_generator_degree_ne_zero :
    (Polynomial.map
      (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField)
      BinaryCyclicGolayPolynomial.generator).degree ≠ 0 := by
  intro hdeg
  have hlt :
      (Polynomial.map
        (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField)
        BinaryCyclicGolayPolynomial.generator).degree < (11 : WithBot ℕ) := by
    rw [hdeg]
    norm_num
  have hcoeff :=
    (Polynomial.degree_lt_iff_coeff_zero
      (Polynomial.map
        (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField)
        BinaryCyclicGolayPolynomial.generator) 11).mp hlt 11 le_rfl
  have hone :
      (Polynomial.map
        (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField)
        BinaryCyclicGolayPolynomial.generator).coeff 11 = 1 := by
    simp [BinaryCyclicGolayPolynomial.generator, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_one]
  rw [hone] at hcoeff
  exact one_ne_zero hcoeff

theorem exists_generator_root :
    ∃ a : RootField,
      Polynomial.eval₂
        (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) a
        BinaryCyclicGolayPolynomial.generator = 0 := by
  rcases Polynomial.Splits.exists_eval_eq_zero mapped_generator_splits
      mapped_generator_degree_ne_zero with ⟨a, ha⟩
  exact ⟨a, by simpa only [Polynomial.eval_map] using ha⟩

theorem eval₂_frobenius_square (a : RootField) (p : Polynomial BinaryCyclicGolayPolynomial.F₂) :
    Polynomial.eval₂
        (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) (a ^ 2) p =
      (Polynomial.eval₂
        (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) a p) ^ 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hchar : (1 : RootField) + 1 = 0 := by
    have h : (1 : BinaryCyclicGolayPolynomial.F₂) + 1 = 0 := by decide
    simpa only [map_add, map_zero, map_one] using
      congrArg (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) h
  have htwo : (2 : RootField) = 0 := by
    calc
      (2 : RootField) = 1 + 1 := by ring
      _ = 0 := hchar
  have hcoeff (c : BinaryCyclicGolayPolynomial.F₂) :
      (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField c) ^ 2 =
        algebraMap BinaryCyclicGolayPolynomial.F₂ RootField c := by
    rw [← map_pow]
    simpa using (ZMod.pow_card c)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hsquare (x y : RootField) :
          (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
        calc
          (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
          _ = x ^ 2 + y ^ 2 := by rw [htwo]; ring
      rw [Polynomial.eval₂_add, hp, hq, Polynomial.eval₂_add, hsquare]
  | monomial n c =>
      rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
      rw [pow_two, mul_pow]
      calc
        (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField c) *
              (a ^ n * a ^ n) =
            (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField c) ^ 2 *
              (a ^ n * a ^ n) := by rw [hcoeff]
        _ = ((algebraMap BinaryCyclicGolayPolynomial.F₂ RootField c) *
              a ^ n) ^ 2 := by ring

theorem generator_root_frobenius_square {a : RootField}
    (ha : Polynomial.eval₂
      (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) a
      BinaryCyclicGolayPolynomial.generator = 0) :
    Polynomial.eval₂
      (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) (a ^ 2)
      BinaryCyclicGolayPolynomial.generator = 0 := by
  rw [eval₂_frobenius_square]
  rw [ha]
  simp

theorem generator_root_frobenius_pow {a : RootField}
    (ha : Polynomial.eval₂
      (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) a
      BinaryCyclicGolayPolynomial.generator = 0) (k : ℕ) :
    Polynomial.eval₂
      (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) (a ^ (2 ^ k))
      BinaryCyclicGolayPolynomial.generator = 0 := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
      have hnext := generator_root_frobenius_square (a := a ^ (2 ^ k)) ih
      have harg : (a ^ (2 ^ k)) ^ 2 = a ^ (2 ^ (Nat.succ k)) := by
        rw [pow_two, pow_succ, ← pow_add]
        congr 1
        omega
      rw [harg] at hnext
      exact hnext

theorem exists_generator_root_order_twenty_three :
    ∃ a : RootField, orderOf a = 23 := by
  rcases exists_generator_root with ⟨a, ha⟩
  have hchar : (1 : RootField) + 1 = 0 := by
    have hbase :
        (1 : BinaryCyclicGolayPolynomial.F₂) + 1 = 0 := by
      decide
    simpa only [map_add, map_zero, map_one] using
      congrArg
        (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) hbase
  have hnegone : -(1 : RootField) = 1 :=
    (neg_eq_iff_add_eq_zero).2 hchar
  have heval :
      Polynomial.eval₂
          (algebraMap BinaryCyclicGolayPolynomial.F₂ RootField) a
          (Polynomial.X ^ 23 + 1) = 0 := by
    rcases BinaryCyclicGolayPolynomial.generator_dvd_x23_add_one with
      ⟨q, hq⟩
    rw [hq, Polynomial.eval₂_mul, ha, zero_mul]
  have hpow' : a ^ 23 + 1 = 0 := by
    simpa [Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X] using heval
  have hpow : a ^ 23 = 1 := by
    have hneg := eq_neg_of_add_eq_zero_left hpow'
    simpa [hnegone] using hneg
  have hne : a ≠ 1 := by
    intro hone
    rw [hone] at ha
    have ha' :
        (1 : RootField) + 1 + 1 + 1 + 1 + 1 + 1 = 0 := by
      simpa [Polynomial.eval₂_add, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, BinaryCyclicGolayPolynomial.generator] using ha
    have hsum :
        (1 : RootField) + 1 + 1 + 1 + 1 + 1 + 1 = 1 := by
      simp [hchar]
    rw [hsum] at ha'
    exact one_ne_zero ha'
  letI : Fact (Nat.Prime 23) := ⟨by decide⟩
  exact ⟨a, (orderOf_eq_prime_iff).2 ⟨hpow, hne⟩⟩

end InfoGeometry.Combinatorics.BinaryGolayRootField
