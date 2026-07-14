import Mathlib

/-!
# Finite prime boson/fermion cancellation

Finite algebraic theorem:

  `(∏ p ∈ S, (1 - x p)⁻¹) * (∏ p ∈ S, (1 - x p)) = 1`

under the local nonzero condition `1 - x p ≠ 0`.

This is the finite theorem-root behind the formal cancellation
`ζ(s) * (1 / ζ(s)) = 1`, but no infinite product or zeta claim is made here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeBosonFermionGas

open scoped BigOperators

variable {ι R : Type*} [Field R]

/-- Finite signed fermion / Möbius Euler factor product. -/
def signedFermionPartition (S : Finset ι) (x : ι → R) : R :=
  ∏ p ∈ S, (1 - x p)

/-- Finite positive fermion Euler factor product. -/
def positiveFermionPartition (S : Finset ι) (x : ι → R) : R :=
  ∏ p ∈ S, (1 + x p)

/-- Finite boson Euler factor product. -/
def bosonPartition (S : Finset ι) (x : ι → R) : R :=
  ∏ p ∈ S, (1 - x p)⁻¹

omit [Field R] in
lemma signedFermionPartition_pos
    (S : Finset ι) (x : ι → ℝ)
    (h : ∀ p ∈ S, 0 < 1 - x p) :
    0 < signedFermionPartition S x := by
  unfold signedFermionPartition
  exact Finset.prod_pos h

omit [Field R] in
lemma positiveFermionPartition_pos
    (S : Finset ι) (x : ι → ℝ)
    (h : ∀ p ∈ S, 0 < 1 + x p) :
    0 < positiveFermionPartition S x := by
  unfold positiveFermionPartition
  exact Finset.prod_pos h

omit [Field R] in
lemma bosonPartition_pos
    (S : Finset ι) (x : ι → ℝ)
    (h : ∀ p ∈ S, 0 < 1 - x p) :
    0 < bosonPartition S x := by
  unfold bosonPartition
  exact Finset.prod_pos (fun p hp => inv_pos.mpr (h p hp))

/--
Finite boson × signed-fermion cancellation.

This is the real algebraic lemma:
the inverse Euler factors cancel the signed fermion Euler factors.
-/
theorem boson_mul_signedFermion_cancel
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    bosonPartition S x * signedFermionPartition S x = 1 := by
  unfold bosonPartition signedFermionPartition
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p hp
  exact inv_mul_cancel₀ (h p hp)

/--
Finite signed-fermion × boson cancellation.

Same result with the factors reversed.
-/
theorem signedFermion_mul_boson_cancel
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    signedFermionPartition S x * bosonPartition S x = 1 := by
  unfold bosonPartition signedFermionPartition
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p hp
  exact mul_inv_cancel₀ (h p hp)

/--
The finite bosonic primon Euler product is nonzero on the regulated domain.

This is the finite algebraic boundary behind the analytic statement that the
reciprocal supertrace can only become singular when the bosonic partition
ceases to be invertible.
-/
theorem bosonPartition_ne_zero
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    bosonPartition S x ≠ 0 := by
  intro hzero
  have hcancel := boson_mul_signedFermion_cancel S x h
  rw [hzero, zero_mul] at hcancel
  exact zero_ne_one hcancel

/--
The finite signed fermion / Möbius Euler product is nonzero on the same
regulated domain.
-/
theorem signedFermionPartition_ne_zero
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    signedFermionPartition S x ≠ 0 := by
  intro hzero
  have hcancel := signedFermion_mul_boson_cancel S x h
  rw [hzero, zero_mul] at hcancel
  exact zero_ne_one hcancel

/--
Finite positive-fermion / boson identity.

This is the finite algebraic shadow of
`∏ₚ (1 + p^{-s}) = ζ(s) / ζ(2s)`: after multiplying the bosonic product by
the square-energy signed factor `∏ₚ (1 - xₚ²)`, one obtains the positive
fermion product `∏ₚ (1 + xₚ)`.
-/
theorem boson_mul_square_signedFermion_eq_positiveFermion
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0) :
    bosonPartition S x * signedFermionPartition S (fun p => x p * x p) =
      positiveFermionPartition S x := by
  unfold bosonPartition signedFermionPartition positiveFermionPartition
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  calc
    (1 - x p)⁻¹ * (1 - x p * x p)
        = (1 - x p)⁻¹ * ((1 - x p) * (1 + x p)) := by ring
    _ = ((1 - x p)⁻¹ * (1 - x p)) * (1 + x p) := by ring
    _ = 1 * (1 + x p) := by rw [inv_mul_cancel₀ (h p hp)]
    _ = 1 + x p := by ring

/--
Finite ratio form of the positive-fermion identity:
`Z_f^+(x) * Z_b(x²) = Z_b(x)`.
-/
theorem positiveFermion_mul_squareBoson_eq_boson
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0)
    (h_sq : ∀ p ∈ S, 1 - x p * x p ≠ 0) :
    positiveFermionPartition S x * bosonPartition S (fun p => x p * x p) =
      bosonPartition S x := by
  rw [← boson_mul_square_signedFermion_eq_positiveFermion S x h]
  calc
    (bosonPartition S x * signedFermionPartition S (fun p => x p * x p)) *
        bosonPartition S (fun p => x p * x p)
        = bosonPartition S x *
            (signedFermionPartition S (fun p => x p * x p) *
              bosonPartition S (fun p => x p * x p)) := by ring
    _ = bosonPartition S x * 1 := by
          rw [signedFermion_mul_boson_cancel S (fun p => x p * x p) h_sq]
    _ = bosonPartition S x := by ring

/--
The finite positive fermion Euler product is nonzero wherever both the
one-prime and square-energy bosonic regulators are defined.
-/
theorem positiveFermionPartition_ne_zero
    (S : Finset ι)
    (x : ι → R)
    (h : ∀ p ∈ S, 1 - x p ≠ 0)
    (h_sq : ∀ p ∈ S, 1 - x p * x p ≠ 0) :
    positiveFermionPartition S x ≠ 0 := by
  intro hzero
  have hratio := positiveFermion_mul_squareBoson_eq_boson S x h h_sq
  rw [hzero, zero_mul] at hratio
  exact (bosonPartition_ne_zero S x h) hratio.symm

/-! ## Real lemma: logarithm of a positive finite product -/

/--
For a positive finite family, the logarithm of the product is the sum of the
logarithms.

This is the direct proof needed for prime log-volume:
`log (∏ p, v p) = ∑ p, log (v p)`.
No certificate field, no wrapper structure.
-/
theorem log_prod_of_pos
    {ι : Type*}
    (s : Finset ι)
    (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) :
    Real.log (s.prod f) = s.sum (fun i => Real.log (f i)) := by
  refine Real.log_prod ?_
  intro i hi
  exact ne_of_gt (hf i hi)

/-! ## Real lemma: finite log-volume factorization with occupations -/

/--
For a positive real number `x`, `log (x^n) = n * log x`.
-/
theorem log_pow_nat_of_pos
    (x : ℝ)
    (n : ℕ)
    (hx : 0 < x) :
    Real.log (x ^ n) = (n : ℝ) * Real.log x := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hxpow : 0 < x ^ n := pow_pos hx n
      rw [pow_succ]
      rw [Real.log_mul (ne_of_gt hxpow) (ne_of_gt hx)]
      rw [ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring

/--
Finite log-volume factorization:

`log (∏ i in s, v i ^ a i) = ∑ i in s, (a i) * log (v i)`,
for positive mode volumes `v i`.
-/
theorem log_prod_pow_of_pos
    {ι : Type*}
    (s : Finset ι)
    (v : ι → ℝ)
    (a : ι → ℕ)
    (hv : ∀ i ∈ s, 0 < v i) :
    Real.log (Finset.prod s (fun i => v i ^ a i)) =
      Finset.sum s (fun i => (a i : ℝ) * Real.log (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s his ih =>
      have hvi : 0 < v i := hv i (by simp)
      have hvs : ∀ j ∈ s, 0 < v j := by
        intro j hj
        exact hv j (by simp [hj])
      have hpow_i : 0 < v i ^ a i := pow_pos hvi (a i)
      have hprod_s : 0 < Finset.prod s (fun j => v j ^ a j) := by
        exact Finset.prod_pos (fun j hj => pow_pos (hvs j hj) (a j))
      rw [Finset.prod_insert his, Finset.sum_insert his]
      rw [Real.log_mul (ne_of_gt hpow_i) (ne_of_gt hprod_s)]
      rw [log_pow_nat_of_pos (v i) (a i) hvi]
      rw [ih hvs]

/--
Prime-volume specialization of finite log-volume factorization.

For positive natural modes on a finite support:

`log (∏ i in s, (i:ℝ)^(a i)) = ∑ i in s, (a i) * log (i:ℝ)`.
-/
theorem log_prod_prime_pow_of_pos
    (s : Finset ℕ)
    (a : ℕ → ℕ)
    (hs : ∀ i ∈ s, 0 < i) :
    Real.log (Finset.prod s (fun i => (i : ℝ) ^ a i)) =
      Finset.sum s (fun i => (a i : ℝ) * Real.log (i : ℝ)) := by
  refine log_prod_pow_of_pos (s := s) (v := fun i => (i : ℝ)) (a := a) ?_
  intro i hi
  have hi' : (0 : ℝ) < (i : ℝ) := by
    exact_mod_cast hs i hi
  simpa using hi'

/--
Prime-specialized finite log-volume factorization.

If every index in `s` is prime, positivity is automatic, so
`log (∏ i∈s, i^(a i)) = ∑ i∈s (a i) log i`.
-/
theorem log_prod_prime_pow_of_prime
    (s : Finset ℕ)
    (a : ℕ → ℕ)
    (hprime : ∀ i ∈ s, Nat.Prime i) :
    Real.log (Finset.prod s (fun i => (i : ℝ) ^ a i)) =
      Finset.sum s (fun i => (a i : ℝ) * Real.log (i : ℝ)) := by
  refine log_prod_prime_pow_of_pos (s := s) (a := a) ?_
  intro i hi
  exact Nat.Prime.pos (hprime i hi)

end InfoGeometry.Arithmetic.PrimeBosonFermionGas
