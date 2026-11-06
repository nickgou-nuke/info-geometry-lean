/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.IsotropicCyclotomicGalois
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.NoncommRing

/-! # Operator cyclotomic identities from nilpotent operators

The cyclotomic polynomials and commutator are reused from the isotropic
cyclotomic owner. This file proves generic ring identities for cube-zero
operators and the ordered Bruhat product. It does not infer a physical
parafermion representation or a Coxeter classification from an arbitrary
operator-valued coefficient.
-/

namespace InfoGeometry.Algebra.OperatorCyclotomicParafermions

open InfoGeometry.Algebra.IsotropicCyclotomicGalois
open InfoGeometry.Algebra.IsotropicCyclotomicGenesis

variable {B : Type*} [Ring B]

/-- Ordered product of two elementary unipotent factors. -/
def bruhat (u v : B) : B := (1 + u) * (1 - v)

/-- The inverse candidate reverses the order of the nilpotent factors. -/
def bruhatInv (u v : B) : B := (1 + v) * (1 - u)

/-- Conjugation by the cubic-unipotent unit `1 + a`, written using its
cyclotomic inverse `Φ₆(a) = 1 - a + a²`. -/
def cubeZeroConj (a x : B) : B := (1 + a) * x * cyclo6 a

/-- The inverse conjugation uses the inverse unit on the left and its inverse
on the right. -/
def cubeZeroConjInv (a x : B) : B := cyclo6 a * x * (1 + a)

/-- Recursive powers used by the all-index cyclotomic identities. -/
def operatorPower : ℕ → B → B
  | 0, _ => 1
  | n + 1, x => operatorPower n x * x

/-- The geometric sum `1 + x + ... + x^(n-1)`, defined without division. -/
def operatorGeometricSum : ℕ → B → B
  | 0, _ => 0
  | n + 1, x => operatorGeometricSum n x + operatorPower n x

/-- An ordered, unnormalized conjugation sum. Before imposing `x^n = 1`,
its commutator with `x` is the difference of the two endpoint terms. -/
def parafermionReynoldsRaw : ℕ → B → B → B
  | 0, _, _ => 0
  | n + 1, x, y => x * parafermionReynoldsRaw n x y + y * operatorPower n x

/-- The clock-weighted raw intertwiner is obtained by multiplying the
telescoping sum on the left by the clock operator. This is not normalized by
the order and is not asserted to be an idempotent averaging operator. -/
def parafermionReynolds (n : ℕ) (x y : B) : B :=
  x * parafermionReynoldsRaw n x y

/-- Conjugation by the unipotent `1 - x`, using the finite geometric sum as
its inverse whenever a suitable power of `x` vanishes. -/
def paraUnipotentConj (n : ℕ) (x y : B) : B :=
  (1 - x) * y * operatorGeometricSum n x

/-- The reverse conjugation associated with `paraUnipotentConj`. -/
def paraUnipotentConjInv (n : ℕ) (x y : B) : B :=
  operatorGeometricSum n x * y * (1 - x)

/-- The recursive operator powers agree with the standard natural powers.
This bridge lets the recursive all-index proofs be used with Mathlib's
ordinary power and finite-sum APIs. -/
theorem operatorPower_eq_pow (n : ℕ) (x : B) :
    operatorPower n x = x ^ n := by
  induction n with
  | zero => simp [operatorPower]
  | succ n ih =>
      rw [operatorPower, ih, pow_succ]

/-- The recursive geometric sum is the usual `Finset.range` sum of powers. -/
theorem operatorGeometricSum_eq_range_sum (n : ℕ) (x : B) :
    operatorGeometricSum n x = ∑ i ∈ Finset.range n, x ^ i := by
  induction n with
  | zero => simp [operatorGeometricSum]
  | succ n ih =>
      change operatorGeometricSum n x + operatorPower n x =
        ∑ i ∈ Finset.range (n + 1), x ^ i
      rw [ih, operatorPower_eq_pow, Finset.sum_range_succ]

/-- The recursive Reynolds operator is the finite ordered conjugation sum
`∑ i < n, x^(n-1-i) * y * x^i`. The order of factors is retained; no
commutativity of `B` is assumed. -/
theorem parafermionReynoldsRaw_eq_range_sum (n : ℕ) (x y : B) :
    parafermionReynoldsRaw n x y =
      ∑ i ∈ Finset.range n,
        operatorPower (n - 1 - i) x * y * operatorPower i x := by
  have hpowerCommutes : ∀ k : ℕ,
      x * operatorPower k x = operatorPower k x * x := by
    intro k
    induction k with
    | zero => simp [operatorPower]
    | succ k ih =>
        simp only [operatorPower]
        calc
          x * (operatorPower k x * x) =
              (x * operatorPower k x) * x := by rw [mul_assoc]
          _ = (operatorPower k x * x) * x := by rw [ih]
  induction n with
  | zero => simp [parafermionReynoldsRaw]
  | succ n ih =>
      simp only [parafermionReynoldsRaw]
      have hindices : ∀ i ∈ Finset.range n, n - i = n - 1 - i + 1 := by
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        omega
      have hterms : ∀ i ∈ Finset.range n,
          x * (operatorPower (n - 1 - i) x * y * operatorPower i x) =
            operatorPower (n - i) x * y * operatorPower i x := by
        intro i hi
        rw [hindices i hi]
        calc
          x * (operatorPower (n - 1 - i) x * y * operatorPower i x) =
              (x * operatorPower (n - 1 - i) x) * y * operatorPower i x := by
                noncomm_ring
          _ = (operatorPower (n - 1 - i) x * x) * y * operatorPower i x := by
                rw [hpowerCommutes]
          _ = operatorPower (n - 1 - i + 1) x * y * operatorPower i x := rfl
      have htail :
          operatorPower (n + 1 - 1 - n) x * y * operatorPower n x =
            y * operatorPower n x := by
        have hidx : n + 1 - 1 - n = 0 := by omega
        rw [hidx]
        simp [operatorPower]
      have hleftSum (f : ℕ → B) (s : Finset ℕ) :
          x * (∑ i ∈ s, f i) = ∑ i ∈ s, x * f i := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
            simp only [Finset.sum_insert ha, mul_add, ih]
      calc
        x * parafermionReynoldsRaw n x y + y * operatorPower n x =
          x * (∑ i ∈ Finset.range n,
            operatorPower (n - 1 - i) x * y * operatorPower i x) +
              y * operatorPower n x := by rw [ih]
        _ =
          (∑ i ∈ Finset.range n,
            operatorPower (n - i) x * y * operatorPower i x) +
            y * operatorPower n x := by
              rw [hleftSum]
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              exact hterms i hi
        _ = ∑ i ∈ Finset.range (n + 1),
            operatorPower (n + 1 - 1 - i) x * y * operatorPower i x := by
              rw [Finset.sum_range_succ]
              rw [htail.symm]
              apply congrArg (fun z : B => z +
                operatorPower (n + 1 - 1 - n) x * y * operatorPower n x)
              apply Finset.sum_congr rfl
              intro i hi
              have hi' : i < n := Finset.mem_range.mp hi
              have hidx : n + 1 - 1 - i = n - i := by omega
              rw [hidx]

/-- Standard-power form of the ordered Reynolds expansion. The clock powers
remain on their original sides of `y`; this is a noncommutative identity. -/
theorem parafermionReynoldsRaw_eq_pow_range_sum (n : ℕ) (x y : B) :
    parafermionReynoldsRaw n x y =
      ∑ i ∈ Finset.range n, x ^ (n - 1 - i) * y * x ^ i := by
  rw [parafermionReynoldsRaw_eq_range_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [operatorPower_eq_pow]

/-- Standard-power expansion of the clock-weighted Reynolds operator. The
leftmost clock factor raises each left exponent by one; the middle operator
is never commuted past a power. -/
theorem parafermionReynolds_eq_pow_range_sum (n : ℕ) (x y : B) :
    parafermionReynolds n x y =
      ∑ i ∈ Finset.range n, x ^ (n - i) * y * x ^ i := by
  unfold parafermionReynolds
  rw [parafermionReynoldsRaw_eq_pow_range_sum]
  have hpowerCommutes : ∀ k : ℕ,
      x * operatorPower k x = operatorPower k x * x := by
    intro k
    induction k with
    | zero => simp [operatorPower]
    | succ k ih =>
        simp only [operatorPower]
        calc
          x * (operatorPower k x * x) =
              (x * operatorPower k x) * x := by rw [mul_assoc]
          _ = (operatorPower k x * x) * x := by rw [ih]
  have hleft (i : ℕ) (hi : i ∈ Finset.range n) :
      x * (x ^ (n - 1 - i) * y * x ^ i) = x ^ (n - i) * y * x ^ i := by
    have hi' : i < n := Finset.mem_range.mp hi
    have hidx : n - i = n - 1 - i + 1 := by omega
    have hpow : x * x ^ (n - 1 - i) = x ^ (n - 1 - i) * x := by
      calc
        x * x ^ (n - 1 - i) = x * operatorPower (n - 1 - i) x := by
          rw [operatorPower_eq_pow]
        _ = operatorPower (n - 1 - i) x * x :=
          hpowerCommutes (n - 1 - i)
        _ = x ^ (n - 1 - i) * x := by rw [operatorPower_eq_pow]
    calc
      x * (x ^ (n - 1 - i) * y * x ^ i) =
          (x * x ^ (n - 1 - i)) * y * x ^ i := by noncomm_ring
      _ = (x ^ (n - 1 - i) * x) * y * x ^ i := by
          rw [hpow]
      _ = x ^ (n - 1 - i + 1) * y * x ^ i := by rw [← pow_succ]
      _ = x ^ (n - i) * y * x ^ i := by rw [hidx]
  have hsum (f : ℕ → B) :
      x * (∑ i ∈ Finset.range n, f i) =
        ∑ i ∈ Finset.range n, x * f i := by
    have hsumAux : ∀ s : Finset ℕ,
        x * (∑ i ∈ s, f i) = ∑ i ∈ s, x * f i := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          simp only [Finset.sum_insert ha, mul_add, ih]
    exact hsumAux _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact hleft i hi

private theorem parafermionReynoldsRaw_zero (n : ℕ) (x : B) :
    parafermionReynoldsRaw n x 0 = 0 := by
  induction n with
  | zero => simp [parafermionReynoldsRaw]
  | succ n ih => simp [parafermionReynoldsRaw, ih]

private theorem parafermionReynoldsRaw_add (n : ℕ) (x y z : B) :
    parafermionReynoldsRaw n x (y + z) =
      parafermionReynoldsRaw n x y + parafermionReynoldsRaw n x z := by
  induction n with
  | zero => simp [parafermionReynoldsRaw]
  | succ n ih =>
      simp only [parafermionReynoldsRaw, ih, add_mul, mul_add]
      abel

/-- The Reynolds operator on the additive group of the coefficient ring. -/
def parafermionReynoldsAddHom (n : ℕ) (x : B) : B →+ B where
  toFun := parafermionReynolds n x
  map_zero' := by simp [parafermionReynolds, parafermionReynoldsRaw_zero]
  map_add' y z := by
    simp only [parafermionReynolds, parafermionReynoldsRaw_add, mul_add]

/-- The ordered Bruhat product of two square-zero elements is a unit with
the reversed product as inverse. Its quadratic relation and the three
displayed cyclotomic evaluations are identities in the same associative
ring. These identities alone do not identify a Coxeter group or classify
its finite reflection orders. -/
theorem bruhat_cyclotomic_characteristic (u v : B)
    (hu : u * u = 0) (hv : v * v = 0) :
    bruhat u v * bruhatInv u v = 1 ∧
    bruhatInv u v * bruhat u v = 1 ∧
    bruhat u v + bruhatInv u v =
      (2 : ℤ) • (1 : B) - anticommutator u v ∧
    InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
      (bruhat u v) (anticommutator u v) = 0 ∧
    bruhat u v * bruhat u v -
        ((2 : ℤ) • (1 : B) - anticommutator u v) * bruhat u v + 1 = 0 ∧
    cyclo6 (bruhat u v) = (1 - anticommutator u v) * bruhat u v ∧
    cyclo4 (bruhat u v) =
      ((2 : ℤ) • (1 : B) - anticommutator u v) * bruhat u v ∧
    cyclo3 (bruhat u v) =
      ((3 : ℤ) • (1 : B) - anticommutator u v) * bruhat u v := by
  simp only [bruhat, bruhatInv, cyclo6, cyclo4, cyclo3,
    anticommutator, InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v]

/-- Exact expansions of the two complements of the ordered Bruhat units.
The signs depend on the order of the factors: `1 - bruhat u v` is
`uv - u + v`, while the reversed unit has complement `vu + u - v`.
These formulas require no nilpotency assumptions. -/
theorem bruhat_complements (u v : B) :
    1 - bruhat u v = u * v - u + v ∧
    1 - bruhatInv u v = v * u + u - v ∧
    bruhat (-u) (-v) = 1 - (u * v + u - v) := by
  unfold bruhat bruhatInv
  constructor
  · noncomm_ring
  constructor
  · noncomm_ring
  · noncomm_ring

/-- A sixth-cyclotomic relation implies the cube of the operator is `-1`.
No commutativity assumption is needed because every factor is a power of the
same operator. -/
theorem cyclo6_root_cube_eq_neg_one (x : B) (h : cyclo6 x = 0) :
    x * x * x = -1 := by
  have hsq : x * x = x - 1 := by
    dsimp [cyclo6] at h ⊢
    calc
      x * x = (x * x - x + 1) + x - 1 := by noncomm_ring
      _ = 0 + x - 1 := by rw [h]
      _ = x - 1 := by noncomm_ring
  calc
    x * x * x = (x * x) * x := by noncomm_ring
    _ = (x - 1) * x := by rw [hsq]
    _ = -1 := by rw [sub_mul, one_mul, hsq]; noncomm_ring

/-- A third-cyclotomic relation implies the cube of the operator is `1`. -/
theorem cyclo3_root_cube_eq_one (x : B) (h : cyclo3 x = 0) :
    x * x * x = 1 := by
  have hsq : x * x = -(x + 1) := by
    dsimp [cyclo3] at h ⊢
    calc
      x * x = (x * x + x + 1) - x - 1 := by noncomm_ring
      _ = 0 - x - 1 := by rw [h]
      _ = -(x + 1) := by noncomm_ring
  calc
    x * x * x = (x * x) * x := by noncomm_ring
    _ = -(x + 1) * x := by rw [hsq]
    _ = 1 := by rw [neg_mul, add_mul, one_mul, hsq]; abel

/-- A fourth-cyclotomic relation makes the square an involution. -/
theorem cyclo4_root_fourth_power_eq_one (x : B) (h : cyclo4 x = 0) :
    x * x * x * x = 1 := by
  have hsq : x * x = -1 := by
    dsimp [cyclo4] at h ⊢
    calc
      x * x = (x * x + 1) - 1 := by noncomm_ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by noncomm_ring
  calc
    x * x * x * x = (x * x) * (x * x) := by noncomm_ring
    _ = 1 := by rw [hsq]; noncomm_ring

/-- The metric specializations of the ordered Bruhat product give actual
third-, fourth-, and sixth-power identities. These are conditional operator
identities, not a Coxeter classification theorem. -/
theorem bruhat_metric_cyclotomic_specializations (u v : B)
    (hu : u * u = 0) (hv : v * v = 0) :
    (anticommutator u v = 1 →
      cyclo6 (bruhat u v) = 0 ∧ bruhat u v * bruhat u v * bruhat u v = -1 ∧
        bruhat u v * bruhat u v * bruhat u v * bruhat u v *
          bruhat u v * bruhat u v = 1) ∧
    (anticommutator u v = (2 : ℤ) • (1 : B) →
      cyclo4 (bruhat u v) = 0 ∧
        bruhat u v * bruhat u v * bruhat u v * bruhat u v = 1) ∧
    (anticommutator u v = (3 : ℤ) • (1 : B) →
      cyclo3 (bruhat u v) = 0 ∧
        bruhat u v * bruhat u v * bruhat u v = 1) := by
  obtain ⟨_, _, _, _, _, h6, h4, h3⟩ :=
    bruhat_cyclotomic_characteristic u v hu hv
  refine ⟨?_, ?_, ?_⟩
  · intro hV
    have hroot : cyclo6 (bruhat u v) = 0 := by
      rw [hV] at h6
      simpa using h6
    have hcube := cyclo6_root_cube_eq_neg_one (bruhat u v) hroot
    refine ⟨hroot, hcube, ?_⟩
    calc
      bruhat u v * bruhat u v * bruhat u v * bruhat u v *
          bruhat u v * bruhat u v =
          (bruhat u v * bruhat u v * bruhat u v) *
            (bruhat u v * bruhat u v * bruhat u v) := by noncomm_ring
      _ = 1 := by rw [hcube]; noncomm_ring
  · intro hV
    have hroot : cyclo4 (bruhat u v) = 0 := by
      rw [hV] at h4
      simpa using h4
    exact ⟨hroot, cyclo4_root_fourth_power_eq_one _ hroot⟩
  · intro hV
    have hroot : cyclo3 (bruhat u v) = 0 := by
      rw [hV] at h3
      simpa using h3
    exact ⟨hroot, cyclo3_root_cube_eq_one _ hroot⟩

/-- The square-zero Bruhat product, packaged as an actual unit. Keeping the
unit carrier explicit lets later group-valued constructions use the same
operator proved cyclotomic above, without treating an inverse equation as a
group representation by itself. -/
def bruhatUnit (u v : B) (hu : u * u = 0) (hv : v * v = 0) : Bˣ :=
  ⟨bruhat u v, bruhatInv u v,
    (bruhat_cyclotomic_characteristic u v hu hv).1,
    (bruhat_cyclotomic_characteristic u v hu hv).2.1⟩

/-- On the unit-support shell, the Bruhat operator is both a sixth
cyclotomic root in the ring and a sixth-power-one element of the unit group.
The shell assumption is essential: off shell the exact defect is
`(1 - (uv + vu)) * bruhat u v`. -/
theorem bruhatUnit_sixth_power_on_shell (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hV : anticommutator u v = 1) :
    bruhatUnit u v hu hv ^ 6 = 1 ∧
    cyclo6 (bruhatUnit u v hu hv : B) = 0 := by
  have hspec := bruhat_metric_cyclotomic_specializations u v hu hv
  obtain ⟨hroot, _, hpow⟩ := hspec.1 hV
  constructor
  · apply Units.ext
    change bruhat u v ^ 6 = 1
    calc
      bruhat u v ^ 6 =
          bruhat u v * bruhat u v * bruhat u v * bruhat u v *
            bruhat u v * bruhat u v := by noncomm_ring
      _ = 1 := hpow
  · change cyclo6 (bruhat u v) = 0
    exact hroot

lemma operatorPower_commutes (n : ℕ) (x : B) :
    x * operatorPower n x = operatorPower n x * x := by
  induction n with
  | zero => simp [operatorPower]
  | succ n ih =>
      simp only [operatorPower]
      calc
        x * (operatorPower n x * x) = (x * operatorPower n x) * x := by
          rw [mul_assoc]
        _ = (operatorPower n x * x) * x := by rw [ih]

/-- Repeatedly transporting a mode past a clock with operator-valued phase
`q` produces the ordered power law `x^n y = q^n y x^n`. The phase need only
commute with the clock; it is not assumed to be a scalar or central in `B`. -/
theorem operator_power_braiding (n : ℕ) (x q y : B)
    (hxy : x * y = q * y * x) (hqx : x * q = q * x) :
    operatorPower n x * y = operatorPower n q * y * operatorPower n x := by
  have hpower : ∀ m : ℕ, operatorPower m x * q = q * operatorPower m x := by
    intro m
    induction m with
    | zero => simp [operatorPower]
    | succ m ih =>
        simp only [operatorPower]
        calc
          (operatorPower m x * x) * q =
              operatorPower m x * (x * q) := by rw [mul_assoc]
          _ = operatorPower m x * (q * x) := by rw [hqx]
          _ = (operatorPower m x * q) * x := by rw [mul_assoc]
          _ = (q * operatorPower m x) * x := by rw [ih]
          _ = q * (operatorPower m x * x) := by noncomm_ring
  induction n with
  | zero => simp [operatorPower]
  | succ n ih =>
      simp only [operatorPower]
      calc
        (operatorPower n x * x) * y =
            operatorPower n x * (x * y) := by rw [mul_assoc]
        _ = operatorPower n x * (q * y * x) := by rw [hxy]
        _ = (operatorPower n x * q) * y * x := by noncomm_ring
        _ = (q * operatorPower n x) * y * x := by rw [hpower n]
        _ = q * (operatorPower n x * y) * x := by noncomm_ring
        _ = q * (operatorPower n q * y * operatorPower n x) * x := by rw [ih]
        _ = (q * operatorPower n q) * y * (operatorPower n x * x) := by
              noncomm_ring
        _ = (operatorPower n q * q) * y * (operatorPower n x * x) := by
              rw [operatorPower_commutes n q]
        _ = operatorPower (n + 1) q * y * operatorPower (n + 1) x := by rfl

/-- If the clock has finite order, its operator-valued braid phase power
acts trivially on every mode satisfying the braid relation. -/
theorem finite_clock_order_forces_braiding_phase_stabilization
    (n : ℕ) (x q y : B) (hxy : x * y = q * y * x)
    (hqx : x * q = q * x) (hx : operatorPower n x = 1) :
    operatorPower n q * y = y := by
  have h := operator_power_braiding n x q y hxy hqx
  rw [hx] at h
  simpa only [one_mul, mul_one] using h.symm

/-- The recursively defined powers use the usual additive exponent law.
Associativity suffices; no commutativity of the coefficient ring is used. -/
theorem operatorPower_add (m n : ℕ) (x : B) :
    operatorPower (m + n) x = operatorPower m x * operatorPower n x := by
  induction n with
  | zero => simp [operatorPower]
  | succ n ih =>
      rw [Nat.add_succ, operatorPower, ih, operatorPower]
      simp only [mul_assoc]

/-- Early telescope fact used by the conjugation declarations below. -/
private theorem operator_geometric_sum_telescopes_aux (n : ℕ) (x : B) :
    (1 - x) * operatorGeometricSum n x = 1 - operatorPower n x ∧
    operatorGeometricSum n x * (1 - x) = 1 - operatorPower n x := by
  have hleft : ∀ n : ℕ,
      (1 - x) * operatorGeometricSum n x = 1 - operatorPower n x := by
    intro n
    induction n with
    | zero => simp [operatorGeometricSum, operatorPower]
    | succ n ih =>
        simp only [operatorGeometricSum, operatorPower, mul_add]
        rw [ih]
        noncomm_ring [operatorPower_commutes n x]
  have hright : ∀ n : ℕ,
      operatorGeometricSum n x * (1 - x) = 1 - operatorPower n x := by
    intro n
    induction n with
    | zero => simp [operatorGeometricSum, operatorPower]
    | succ n ih =>
        simp only [operatorGeometricSum, operatorPower, add_mul]
        rw [ih]
        noncomm_ring
  exact ⟨hleft n, hright n⟩

/-- Early inverse consequence used before the public theorem declarations. -/
private theorem operator_geometric_sum_inverse_aux (n : ℕ) (x : B)
    (hnil : operatorPower n x = 0) :
    (1 - x) * operatorGeometricSum n x = 1 ∧
    operatorGeometricSum n x * (1 - x) = 1 := by
  obtain ⟨hl, hr⟩ := operator_geometric_sum_telescopes_aux n x
  rw [hl, hr, hnil]
  simp

/-- Splitting the geometric sum after its first `m` terms leaves a translated
tail. The power multiplies on the left, preserving the order of the original
monomials. -/
theorem operator_geometric_sum_block (m n : ℕ) (x : B) :
    operatorGeometricSum (m + n) x =
      operatorGeometricSum m x + operatorPower m x * operatorGeometricSum n x := by
  induction n with
  | zero => simp [operatorGeometricSum]
  | succ n ih =>
      rw [Nat.add_succ, operatorGeometricSum, ih, operatorGeometricSum,
        operatorPower_add]
      noncomm_ring

/-- A geometric sum in `x` commutes with every power of `x`. -/
theorem operator_geometric_sum_commutes_power (m n : ℕ) (x : B) :
    operatorGeometricSum m x * operatorPower n x =
      operatorPower n x * operatorGeometricSum m x := by
  induction m with
  | zero => simp [operatorGeometricSum]
  | succ m ih =>
      simp only [operatorGeometricSum, add_mul, mul_add, ih]
      have hp : operatorPower m x * operatorPower n x =
          operatorPower n x * operatorPower m x := by
        calc
          operatorPower m x * operatorPower n x = operatorPower (m + n) x :=
            (operatorPower_add m n x).symm
          _ = operatorPower (n + m) x := by rw [Nat.add_comm]
          _ = operatorPower n x * operatorPower m x := operatorPower_add n m x
      rw [hp]

/-- Multiplicative composition of finite geometric sums. The two factors
commute because both are polynomials in the same ring element. -/
theorem operator_geometric_sum_composition (m k : ℕ) (x : B) :
    operatorGeometricSum (m * k) x =
        operatorGeometricSum m x * operatorGeometricSum k (operatorPower m x) ∧
    operatorGeometricSum (m * k) x =
        operatorGeometricSum k (operatorPower m x) * operatorGeometricSum m x := by
  have hpow : ∀ j : ℕ,
      operatorPower j (operatorPower m x) = operatorPower (m * j) x := by
    intro j
    induction j with
    | zero => simp [operatorPower]
    | succ j ih =>
        rw [Nat.mul_succ, operatorPower, ih, operatorPower_add]
  constructor
  · induction k with
    | zero => simp [operatorGeometricSum]
    | succ k ih =>
        rw [Nat.mul_succ, operator_geometric_sum_block, ih]
        simp only [operatorGeometricSum, mul_add, hpow]
        rw [← operator_geometric_sum_commutes_power m (m * k) x]
  · induction k with
    | zero => simp [operatorGeometricSum]
    | succ k ih =>
        rw [Nat.mul_succ, operator_geometric_sum_block, ih]
        simp only [operatorGeometricSum, add_mul, hpow]

/-- Purely square-zero construction of the order-six and order-three
cyclotomic candidates. The identity is off-shell: its remainder is the
support defect `1 - (uv + vu)`. No idempotent is assumed. -/
theorem square_zero_pair_cyclotomic_candidates (u v : B)
    (hu : u * u = 0) (hv : v * v = 0) :
    cyclo6 (u * v + u - v) =
        (1 - (u * v + v * u)) * (1 - (u * v + u - v)) ∧
    cyclo3 (-(u * v + u - v)) =
        (1 - (u * v + v * u)) * (1 - (u * v + u - v)) ∧
    cyclo4 (u - v) = 1 - (u * v + v * u) := by
  have huL : u * (u * v) = 0 := by rw [← mul_assoc, hu, zero_mul]
  have hvL : v * (v * u) = 0 := by rw [← mul_assoc, hv, zero_mul]
  simp only [cyclo3, cyclo4, cyclo6]
  refine ⟨?_, ?_, ?_⟩ <;> noncomm_ring [hu, hv, huL, hvL]

/-- On the unit-support shell, the three square-zero-pair candidates are
actual cyclotomic roots.  This is the precise conditional content of the
order-three, order-four, and order-six clock claims: no background
idempotent or scalar root of unity is required. -/
theorem square_zero_pair_on_shell_cyclotomic_orders (u v : B)
    (hu : u * u = 0) (hv : v * v = 0)
    (hV : anticommutator u v = 1) :
    cyclo6 (u * v + u - v) = 0 ∧
    cyclo3 (-(u * v + u - v)) = 0 ∧
    cyclo4 (u - v) = 0 ∧
    (u * v + u - v) * (u * v + u - v) *
      (u * v + u - v) * (u * v + u - v) *
      (u * v + u - v) * (u * v + u - v) = 1 ∧
    (u * v + u - v) * (u * v + u - v) *
      (u * v + u - v) = -1 ∧
    (-(u * v + u - v)) * (-(u * v + u - v)) *
      (-(u * v + u - v)) = 1 ∧
    (u - v) * (u - v) * (u - v) * (u - v) = 1 := by
  obtain ⟨h6, h3, h4⟩ := square_zero_pair_cyclotomic_candidates u v hu hv
  change u * v + v * u = 1 at hV
  have h6root : cyclo6 (u * v + u - v) = 0 := by
    rw [h6, hV]
    noncomm_ring
  have h3root : cyclo3 (-(u * v + u - v)) = 0 := by
    rw [h3, hV]
    noncomm_ring
  have h4root : cyclo4 (u - v) = 0 := by
    rw [h4, hV]
    noncomm_ring
  refine ⟨h6root, h3root, h4root, ?_, ?_, ?_, ?_⟩
  · have hcube := cyclo6_root_cube_eq_neg_one _ h6root
    calc
      (u * v + u - v) * (u * v + u - v) *
          (u * v + u - v) * (u * v + u - v) *
          (u * v + u - v) * (u * v + u - v) =
          ((u * v + u - v) * (u * v + u - v) *
            (u * v + u - v)) *
          ((u * v + u - v) * (u * v + u - v) *
            (u * v + u - v)) := by noncomm_ring
      _ = 1 := by rw [hcube]; noncomm_ring
  · exact cyclo6_root_cube_eq_neg_one _ h6root
  · exact cyclo3_root_cube_eq_one _ h3root
  · exact cyclo4_root_fourth_power_eq_one _ h4root

/-- The all-order unipotent conjugation has an exact off-shell expansion.
This is an algebraic rearrangement of the geometric telescoping identity;
it does not require nilpotency. -/
theorem para_unipotent_conjugation_off_shell (n : ℕ) (x y : B) :
    paraUnipotentConj n x y =
      y * (1 - operatorPower n x) -
        InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator x y *
          operatorGeometricSum n x := by
  obtain ⟨htel, _⟩ := operator_geometric_sum_telescopes_aux n x
  unfold paraUnipotentConj InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
  have hcomm : (1 - x) * y = y * (1 - x) - (x * y - y * x) := by
    noncomm_ring
  calc
    (1 - x) * y * operatorGeometricSum n x =
        (y * (1 - x) - (x * y - y * x)) * operatorGeometricSum n x := by
          rw [hcomm]
    _ = y * ((1 - x) * operatorGeometricSum n x) -
          (x * y - y * x) * operatorGeometricSum n x := by
            noncomm_ring
    _ = y * (1 - operatorPower n x) -
          (x * y - y * x) * operatorGeometricSum n x := by rw [htel]

/-- If `x^n = 0`, the finite geometric sum is a two-sided inverse of `1-x`.
Consequently the conjugation and reverse conjugation are inverse ring
automorphisms. -/
theorem para_unipotent_conjugation_is_inner_auto (n : ℕ) (x y z : B)
    (hnil : x ^ n = 0) :
    paraUnipotentConj n x y =
        y - InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator x y *
          operatorGeometricSum n x ∧
    paraUnipotentConj n x (paraUnipotentConjInv n x y) = y ∧
    paraUnipotentConjInv n x (paraUnipotentConj n x y) = y ∧
    paraUnipotentConj n x (y * z) =
        paraUnipotentConj n x y * paraUnipotentConj n x z := by
  have hnil' : operatorPower n x = 0 := by
    rw [operatorPower_eq_pow]
    exact hnil
  obtain ⟨hinvL, hinvR⟩ := operator_geometric_sum_inverse_aux n x hnil'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [para_unipotent_conjugation_off_shell, hnil', sub_zero, mul_one]
  · unfold paraUnipotentConj paraUnipotentConjInv
    calc
      (1 - x) * (operatorGeometricSum n x * y * (1 - x)) *
          operatorGeometricSum n x =
        ((1 - x) * operatorGeometricSum n x) * y *
          ((1 - x) * operatorGeometricSum n x) := by noncomm_ring
      _ = y := by rw [hinvL]; noncomm_ring
  · unfold paraUnipotentConj paraUnipotentConjInv
    calc
      operatorGeometricSum n x * ((1 - x) * y * operatorGeometricSum n x) *
          (1 - x) =
        (operatorGeometricSum n x * (1 - x)) * y *
          (operatorGeometricSum n x * (1 - x)) := by noncomm_ring
      _ = y := by rw [hinvR]; noncomm_ring
  · unfold paraUnipotentConj
    calc
      (1 - x) * (y * z) * operatorGeometricSum n x =
          (1 - x) * y * (operatorGeometricSum n x * (1 - x)) *
            z * operatorGeometricSum n x := by rw [hinvR]; noncomm_ring
      _ = ((1 - x) * y * operatorGeometricSum n x) *
            ((1 - x) * z * operatorGeometricSum n x) := by noncomm_ring

/-- Under the nilpotency hypothesis, conjugation by `1 - x` is a unital
ring homomorphism. This packages the additive and unit laws together with
the multiplicativity already proved above, so downstream constructions can
use the canonical `RingHom` interface. -/
def paraUnipotentConjRingHom (n : ℕ) (x : B) (hnil : x ^ n = 0) : B →+* B where
  toFun := paraUnipotentConj n x
  map_zero' := by
    simp [paraUnipotentConj]
  map_one' := by
    have hnil' : operatorPower n x = 0 := by
      rw [operatorPower_eq_pow]
      exact hnil
    obtain ⟨hinv, _⟩ := operator_geometric_sum_inverse_aux n x hnil'
    unfold paraUnipotentConj
    simpa [mul_assoc] using hinv
  map_add' y z := by
    simp only [paraUnipotentConj, mul_add, add_mul, mul_assoc]
  map_mul' y z := by
    exact (para_unipotent_conjugation_is_inner_auto n x y z hnil).2.2.2

private lemma int_smul_add_self (a : ℤ) (x : B) :
    a • x + x = (a + 1) • x := by
  calc
    a • x + x = a • x + (1 : ℤ) • x := by simp
    _ = (a + 1) • x := by rw [← add_zsmul]

/-- The all-index noncommutative geometric-sum identity. -/
theorem operator_geometric_sum_telescopes (n : ℕ) (x : B) :
    (1 - x) * operatorGeometricSum n x = 1 - operatorPower n x ∧
    operatorGeometricSum n x * (1 - x) = 1 - operatorPower n x := by
  have hleft : ∀ n : ℕ,
      (1 - x) * operatorGeometricSum n x = 1 - operatorPower n x := by
    intro n
    induction n with
    | zero => simp [operatorGeometricSum, operatorPower]
    | succ n ih =>
        simp only [operatorGeometricSum, operatorPower, mul_add]
        rw [ih]
        noncomm_ring [operatorPower_commutes n x]
  have hright : ∀ n : ℕ,
      operatorGeometricSum n x * (1 - x) = 1 - operatorPower n x := by
    intro n
    induction n with
    | zero => simp [operatorGeometricSum, operatorPower]
    | succ n ih =>
        simp only [operatorGeometricSum, operatorPower, add_mul]
        rw [ih]
        noncomm_ring
  exact ⟨hleft n, hright n⟩

/-- Vanishing of the finite geometric sum forces the corresponding power to
be one. This is the implication obtained from the telescoping identity;
the converse is not asserted, since `1 - x` need not be cancellable. -/
theorem operator_geometric_sum_zero_implies_power_eq_one (n : ℕ) (x : B)
    (hsum : operatorGeometricSum n x = 0) : operatorPower n x = 1 := by
  have htel := (operator_geometric_sum_telescopes n x).1
  have hzero : 0 = 1 - operatorPower n x := by
    simpa [hsum] using htel
  exact (sub_eq_zero.mp hzero.symm).symm

/-- Standard-power form of `operator_geometric_sum_zero_implies_power_eq_one`.
This is the precise algebraic consequence of a vanishing cyclotomic sum. -/
theorem pow_eq_one_of_operator_geometric_sum_eq_zero (n : ℕ) (x : B)
    (hsum : operatorGeometricSum n x = 0) : x ^ n = 1 := by
  rw [← operatorPower_eq_pow]
  exact operator_geometric_sum_zero_implies_power_eq_one n x hsum

/-- A translated finite window telescopes to the difference of its endpoint
powers. The products remain in the order induced by the window
`x^m, x^(m+1), ..., x^(m+n-1)`. -/
theorem operator_geometric_sum_window (m n : ℕ) (x : B) :
    (1 - x) * (operatorPower m x * operatorGeometricSum n x) =
        operatorPower m x - operatorPower (m + n) x ∧
      (operatorPower m x * operatorGeometricSum n x) * (1 - x) =
        operatorPower m x - operatorPower (m + n) x := by
  obtain ⟨hleft, hright⟩ := operator_geometric_sum_telescopes n x
  constructor
  · calc
      (1 - x) * (operatorPower m x * operatorGeometricSum n x) =
          ((1 - x) * operatorPower m x) * operatorGeometricSum n x := by
            rw [mul_assoc]
      _ = (operatorPower m x * (1 - x)) * operatorGeometricSum n x := by
            congr 1
            noncomm_ring [operatorPower_commutes m x]
      _ = operatorPower m x * ((1 - x) * operatorGeometricSum n x) := by
            rw [mul_assoc]
      _ = operatorPower m x * (1 - operatorPower n x) := by rw [hleft]
      _ = operatorPower m x - operatorPower (m + n) x := by
            rw [operatorPower_add]
            noncomm_ring
  · calc
      (operatorPower m x * operatorGeometricSum n x) * (1 - x) =
          operatorPower m x * (operatorGeometricSum n x * (1 - x)) := by
            rw [mul_assoc]
      _ = operatorPower m x * (1 - operatorPower n x) := by rw [hright]
      _ = operatorPower m x - operatorPower (m + n) x := by
            rw [operatorPower_add]
            noncomm_ring

/-- If `x^n = 0`, the geometric sum is a two-sided inverse of `1 - x`.
This includes the edge case `n = 0`, whose hypothesis forces `1 = 0`. -/
theorem operator_geometric_sum_inverse (n : ℕ) (x : B)
    (hxn : x ^ n = 0) :
    (1 - x) * operatorGeometricSum n x = 1 ∧
    operatorGeometricSum n x * (1 - x) = 1 := by
  obtain ⟨hleft, hright⟩ := operator_geometric_sum_telescopes n x
  have hpow : operatorPower n x = 0 := by
    rw [operatorPower_eq_pow]
    exact hxn
  rw [hpow] at hleft hright
  exact ⟨by simpa using hleft, by simpa using hright⟩

/-- The existing two-sided geometric inverse is the native total ring inverse.
Nilpotence supplies an actual unit, so no nonunit branch of `Ring.inverse` is
used. The statement includes the zero-ring edge case at exponent zero. -/
theorem ringInverse_one_sub_eq_operatorGeometricSum (n : ℕ) (x : B)
    (hxn : x ^ n = 0) :
    Ring.inverse (1 - x) = operatorGeometricSum n x := by
  obtain ⟨hleft, hright⟩ := operator_geometric_sum_inverse n x hxn
  let u : Bˣ := ⟨1 - x, operatorGeometricSum n x, hleft, hright⟩
  exact Ring.inverse_unit u

/-- Native powers and finite sums give the same nilpotent inverse formula. -/
theorem ringInverse_one_sub_eq_sum (n : ℕ) (x : B) (hxn : x ^ n = 0) :
    Ring.inverse (1 - x) = ∑ i ∈ Finset.range n, x ^ i := by
  rw [ringInverse_one_sub_eq_operatorGeometricSum n x hxn,
    operatorGeometricSum_eq_range_sum]

/-- The raw Reynolds sum has a telescoping commutator in every unital
associative ring. -/
theorem parafermion_reynolds_raw_commutator (n : ℕ) (x y : B) :
    InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
      x (parafermionReynoldsRaw n x y) =
      operatorPower n x * y - y * operatorPower n x := by
  induction n with
  | zero => simp [InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator,
    parafermionReynoldsRaw, operatorPower]
  | succ n ih =>
      simp only [parafermionReynoldsRaw, operatorPower,
        InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator]
      calc
        x * (x * parafermionReynoldsRaw n x y + y * operatorPower n x) -
            (x * parafermionReynoldsRaw n x y + y * operatorPower n x) * x =
          x * (x * parafermionReynoldsRaw n x y -
              parafermionReynoldsRaw n x y * x) +
            (x * y * operatorPower n x -
              y * operatorPower n x * x) := by noncomm_ring
        _ = x * InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
              x (parafermionReynoldsRaw n x y) +
              (x * y * operatorPower n x -
                y * operatorPower n x * x) := by rfl
        _ = operatorPower (n + 1) x * y -
              y * operatorPower (n + 1) x := by
          rw [ih]
          simp only [operatorPower]
          have hmove : x * (operatorPower n x * y) =
              operatorPower n x * (x * y) := by
            calc
              x * (operatorPower n x * y) =
                  (x * operatorPower n x) * y := by noncomm_ring
              _ = (operatorPower n x * x) * y := by
                rw [operatorPower_commutes n x]
              _ = operatorPower n x * (x * y) := by noncomm_ring
          rw [mul_sub, hmove]
          noncomm_ring [operatorPower_commutes n x]

/-- When `x^n = 1`, the raw sum is an intertwiner into the centralizer of
`x`; the clock-weighted Reynolds operator is likewise centralizer-valued. -/
theorem parafermion_reynolds_commutes (n : ℕ) (x y : B)
    (hxn : operatorPower n x = 1) :
    InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
      x (parafermionReynoldsRaw n x y) = 0 ∧
    InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
      x (parafermionReynolds n x y) = 0 := by
  have hraw := parafermion_reynolds_raw_commutator n x y
  have hraw0 : InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
      x (parafermionReynoldsRaw n x y) = 0 := by
    rw [hraw, hxn]
    simp
  have hweighted : InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
      x (x * parafermionReynoldsRaw n x y) = 0 := by
    dsimp [InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator] at hraw0 ⊢
    calc
      x * (x * parafermionReynoldsRaw n x y) -
          (x * parafermionReynoldsRaw n x y) * x =
        x * (x * parafermionReynoldsRaw n x y -
          parafermionReynoldsRaw n x y * x) := by noncomm_ring
      _ = 0 := by rw [hraw0]; simp
  exact ⟨hraw0, by simpa [parafermionReynolds] using hweighted⟩

/-- If `y` commutes with the clock, the raw ordered sum reduces to the
integer multiple of its final power term. -/
lemma parafermionReynoldsRaw_commuting (n : ℕ) (x y : B)
    (hxy : x * y = y * x) :
    parafermionReynoldsRaw (n + 1) x y =
      ((n + 1 : ℤ) • (operatorPower n x * y)) := by
  have hpow : ∀ m : ℕ, operatorPower m x * y = y * operatorPower m x := by
    intro m
    induction m with
    | zero => simp [operatorPower]
    | succ m ih =>
        simp only [operatorPower]
        calc
          (operatorPower m x * x) * y =
              operatorPower m x * (x * y) := by rw [mul_assoc]
          _ = operatorPower m x * (y * x) := by rw [hxy]
          _ = (operatorPower m x * y) * x := by rw [mul_assoc]
          _ = (y * operatorPower m x) * x := by rw [ih]
          _ = y * (operatorPower m x * x) := by rw [mul_assoc]
  induction n with
  | zero => simp [parafermionReynoldsRaw, operatorPower]
  | succ n ih =>
      change x * parafermionReynoldsRaw (n + 1) x y +
          y * operatorPower (n + 1) x =
        ((n + 2 : ℤ) • (operatorPower (n + 1) x * y))
      rw [ih]
      have hmove : x * (operatorPower n x * y) =
          operatorPower (n + 1) x * y := by
        calc
          x * (operatorPower n x * y) =
              (x * operatorPower n x) * y := by noncomm_ring
          _ = (operatorPower n x * x) * y := by
            rw [operatorPower_commutes n x]
          _ = operatorPower (n + 1) x * y := by
            rfl
      have hdist : x * ((n + 1 : ℤ) • (operatorPower n x * y)) =
          (n + 1 : ℤ) • (x * (operatorPower n x * y)) := by
        exact AddMonoidHom.map_zsmul (AddMonoidHom.mulLeft x) _ _
      rw [hdist, hmove, hpow (n + 1)]
      let t := y * operatorPower (n + 1) x
      change ((n + 1 : ℤ) • t) + t = (n + 2 : ℤ) • t
      rw [show (n + 2 : ℤ) = (n + 1 : ℤ) + 1 by omega]
      exact int_smul_add_self (n + 1) t

/-- Correct evaluation at the identity for this Reynolds convention:
the `n+1` summands all equal `x^n`. It is generally not the geometric
sum `1+x+...+x^n`. -/
theorem parafermion_reynolds_raw_one (n : ℕ) (x : B) :
    parafermionReynoldsRaw (n + 1) x 1 =
      ((n + 1 : ℤ) • operatorPower n x) := by
  simpa using
    parafermionReynoldsRaw_commuting n x 1 (by simp)

/-- Correct finite-difference specialization of the raw recurrence. Since
`1-x` commutes with `x`, each of its `n+1` summands is the same endpoint
term; this is distinct from the geometric telescoping identity. -/
theorem parafermion_reynolds_raw_coboundary (n : ℕ) (x : B) :
    parafermionReynoldsRaw (n + 1) x (1 - x) =
      ((n + 1 : ℤ) • (operatorPower n x * (1 - x))) := by
  apply parafermionReynoldsRaw_commuting
  noncomm_ring

/-- Correct evaluations of the clock-weighted Reynolds operator at the
identity and at the finite difference `1 - x`.  With the recurrence used
here, its `n + 1` summands have a common endpoint power; they do not form
the geometric sum. -/
theorem parafermion_reynolds_identity_and_coboundary (n : ℕ) (x : B) :
    parafermionReynolds (n + 1) x 1 =
      ((n + 1 : ℤ) • operatorPower (n + 1) x) ∧
    parafermionReynolds (n + 1) x (1 - x) =
      ((n + 1 : ℤ) • (operatorPower (n + 1) x * (1 - x))) := by
  have hscale (z : B) : x * ((n + 1 : ℤ) • z) =
      (n + 1 : ℤ) • (x * z) :=
    AddMonoidHom.map_zsmul (AddMonoidHom.mulLeft x) _ _
  constructor
  · change x * parafermionReynoldsRaw (n + 1) x 1 = _
    rw [parafermion_reynolds_raw_one, hscale]
    rw [operatorPower_commutes n x]
    rfl
  · change x * parafermionReynoldsRaw (n + 1) x (1 - x) = _
    rw [parafermion_reynolds_raw_coboundary, hscale]
    congr 1
    calc
      x * (operatorPower n x * (1 - x)) =
          (x * operatorPower n x) * (1 - x) := by rw [mul_assoc]
      _ = (operatorPower n x * x) * (1 - x) := by
        rw [operatorPower_commutes]
      _ = operatorPower (n + 1) x * (1 - x) := rfl

/-- All-index identity specialization for the clock-weighted Reynolds
operator. At order zero the sum is empty; at positive order its `n` terms
each contribute the same power `x^n`. Thus it is `n • x^n`, not the
geometric sum `1 + x + ⋯ + x^(n-1)`. -/
theorem parafermion_reynolds_identity_all_indices (n : ℕ) (x : B) :
    parafermionReynolds n x 1 = (n : ℤ) • operatorPower n x := by
  cases n with
  | zero => simp [parafermionReynolds, parafermionReynoldsRaw]
  | succ n =>
      simpa using (parafermion_reynolds_identity_and_coboundary n x).1

/-- The matching all-index specialization of the raw Reynolds sum. Its
`n` ordered summands collapse to `n` copies of `x^(n-1)` at the identity.
The zero-order case is the empty sum. -/
theorem parafermion_reynolds_raw_identity_all_indices (n : ℕ) (x : B) :
    parafermionReynoldsRaw n x 1 =
      (n : ℤ) • operatorPower (n - 1) x := by
  cases n with
  | zero => simp [parafermionReynoldsRaw, operatorPower]
  | succ n =>
      simpa using parafermion_reynolds_raw_one n x

/-- Finite Reynolds mode selection for the tetraktys generated by a
square-zero pair. The transverse modes are killed at orders two and four;
the longitudinal modes retain their explicit operator-valued weights. -/
theorem isotropic_tetraktys_reynolds_mode_selection (u v : B)
    (hu : u * u = 0) (hv : v * v = 0) :
    parafermionReynoldsRaw 2 (isotropicDifference u v) (isotropicSum u v) = 0 ∧
    parafermionReynoldsRaw 4 (isotropicDifference u v) (isotropicSum u v) = 0 ∧
    parafermionReynoldsRaw 2 (isotropicDifference u v) (cornerUnit u v) =
      ((2 : ℤ) • (cornerUnit u v * isotropicDifference u v)) ∧
    parafermionReynoldsRaw 2 (isotropicDifference u v)
      (isotropicDifference u v) = -(2 : ℤ) • cornerUnit u v ∧
    parafermionReynoldsRaw 2 (isotropicDifference u v) (pairParity u v) = 0 ∧
    parafermionReynoldsRaw 4 (isotropicDifference u v)
      (isotropicDifference u v) =
      ((4 : ℤ) • (cornerUnit u v * cornerUnit u v)) ∧
    parafermionReynoldsRaw 4 (isotropicDifference u v) (pairParity u v) =
      0 := by
  simp only [parafermionReynoldsRaw, operatorPower,
    isotropicDifference, isotropicSum, cornerUnit, pairParity,
    cornerPlus, cornerMinus]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    noncomm_ring [hu, hv, ← mul_assoc u u, ← mul_assoc v v]

/-- At a positive finite order, the clock-weighted Reynolds sum is a
quasi-projector: `R² = k R`. Its value lies in the centralizer of the clock.
If the integer `k` is invertible and the sum is normalized by `k⁻¹`, this
identity becomes idempotency. -/
theorem parafermion_reynolds_quasi_idempotent (n : ℕ) (x y : B)
    (hxn : operatorPower (n + 1) x = 1) :
    parafermionReynolds (n + 1) x (parafermionReynolds (n + 1) x y) =
      ((n + 1 : ℤ) • parafermionReynolds (n + 1) x y) := by
  let z := parafermionReynolds (n + 1) x y
  have hzcomm := (parafermion_reynolds_commutes (n + 1) x y hxn).2
  have hzx : x * z = z * x := sub_eq_zero.mp (by
    simpa [z, InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator]
      using hzcomm)
  have hraw := parafermionReynoldsRaw_commuting n x z hzx
  have hdist : x * ((n + 1 : ℤ) • (operatorPower n x * z)) =
      (n + 1 : ℤ) • (x * (operatorPower n x * z)) := by
    exact AddMonoidHom.map_zsmul (AddMonoidHom.mulLeft x) _ _
  change x * parafermionReynoldsRaw (n + 1) x z =
    ((n + 1 : ℤ) • z)
  calc
    x * parafermionReynoldsRaw (n + 1) x z =
        x * ((n + 1 : ℤ) • (operatorPower n x * z)) := by rw [hraw]
    _ = (n + 1 : ℤ) • (x * (operatorPower n x * z)) := by
      exact hdist
    _ = (n + 1 : ℤ) • (operatorPower (n + 1) x * z) := by
      congr 1
      calc
        x * (operatorPower n x * z) =
            (x * operatorPower n x) * z := by noncomm_ring
        _ = (operatorPower n x * x) * z := by
          rw [operatorPower_commutes n x]
        _ = operatorPower (n + 1) x * z := by
          simp only [operatorPower]
    _ = (n + 1 : ℤ) • z := by rw [hxn]; simp

/-- On the additive endomorphism carrier, the finite-order Reynolds
intertwiner is quasi-idempotent under composition. This is an operator law;
it does not assert that an individual value in `B` is idempotent. -/
theorem parafermion_reynolds_addHom_quasi_idempotent (n : ℕ) (x : B)
    (hxn : operatorPower (n + 1) x = 1) :
    (parafermionReynoldsAddHom (n + 1) x).comp
        (parafermionReynoldsAddHom (n + 1) x) =
      (n + 1 : ℤ) • parafermionReynoldsAddHom (n + 1) x := by
  ext y
  change parafermionReynolds (n + 1) x
      (parafermionReynolds (n + 1) x y) =
    (n + 1 : ℤ) • parafermionReynolds (n + 1) x y
  exact parafermion_reynolds_quasi_idempotent n x y hxn

/-- Central left multiplication commutes with the finite Reynolds operator
when its coefficient commutes with the clock. -/
theorem parafermion_reynolds_central_left_action (n : ℕ) (x c y : B)
    (hcx : c * x = x * c) :
    parafermionReynolds (n + 1) x (c * y) =
      c * parafermionReynolds (n + 1) x y := by
  have hpow : ∀ m : ℕ, operatorPower m x * c = c * operatorPower m x := by
    intro m
    induction m with
    | zero => simp [operatorPower]
    | succ m ih =>
        simp only [operatorPower]
        calc
          (operatorPower m x * x) * c =
              operatorPower m x * (x * c) := by rw [mul_assoc]
          _ = operatorPower m x * (c * x) := by rw [hcx]
          _ = (operatorPower m x * c) * x := by rw [mul_assoc]
          _ = (c * operatorPower m x) * x := by rw [ih]
          _ = c * operatorPower (m + 1) x := by
            simp only [operatorPower, mul_assoc]
  have hraw : ∀ m : ℕ,
      parafermionReynoldsRaw m x (c * y) =
        c * parafermionReynoldsRaw m x y := by
    intro m
    induction m with
    | zero => simp [parafermionReynoldsRaw]
    | succ m ih =>
        simp only [parafermionReynoldsRaw, ih]
        calc
          x * (c * parafermionReynoldsRaw m x y) +
              c * y * operatorPower m x =
              c * (x * parafermionReynoldsRaw m x y) +
                c * y * operatorPower m x := by
                  calc
                    x * (c * parafermionReynoldsRaw m x y) +
                        c * y * operatorPower m x =
                        (x * c) * parafermionReynoldsRaw m x y +
                          c * y * operatorPower m x := by
                            congr 1
                            rw [mul_assoc]
                    _ = (c * x) * parafermionReynoldsRaw m x y +
                          c * y * operatorPower m x := by rw [hcx.symm]
                    _ = c * (x * parafermionReynoldsRaw m x y) +
                          c * y * operatorPower m x := by
                            simp only [mul_assoc]
          _ = c * (x * parafermionReynoldsRaw m x y +
                y * operatorPower m x) := by
                  calc
                    c * (x * parafermionReynoldsRaw m x y) +
                        c * y * operatorPower m x =
                        c * (x * parafermionReynoldsRaw m x y) +
                          c * (y * operatorPower m x) := by
                            congr 1
                            exact mul_assoc c y (operatorPower m x)
                    _ = c * (x * parafermionReynoldsRaw m x y +
                          y * operatorPower m x) := by rw [mul_add]
  simp only [parafermionReynolds]
  rw [hraw (n + 1)]
  calc
    x * (c * parafermionReynoldsRaw (n + 1) x y) =
        c * (x * parafermionReynoldsRaw (n + 1) x y) := by
          calc
            x * (c * parafermionReynoldsRaw (n + 1) x y) =
                (x * c) * parafermionReynoldsRaw (n + 1) x y := by rw [mul_assoc]
            _ = (c * x) * parafermionReynoldsRaw (n + 1) x y := by rw [hcx]
            _ = c * (x * parafermionReynoldsRaw (n + 1) x y) := by rw [mul_assoc]

/-- Compose the finite Reynolds endomorphism with central normalization.
The displayed inverse condition is needed because division by the order is
not available in an arbitrary ring. -/
def normalizedParafermionReynoldsAddHom (n : ℕ) (x c : B) : B →+ B where
  toFun y := c * parafermionReynolds (n + 1) x y
  map_zero' := by
    simp [parafermionReynolds, parafermionReynoldsRaw_zero]
  map_add' y z := by
    simp only [parafermionReynolds, parafermionReynoldsRaw_add, mul_add]

/-- With a central coefficient `c` satisfying `c*k=1`, the normalized
finite-order Reynolds endomorphism is an idempotent *under composition*.
This is the correct projector conclusion: no elementwise idempotency of
`parafermionReynolds ... y` is asserted. -/
theorem normalized_parafermion_reynolds_comp_idempotent (n : ℕ) (x c : B)
    (hxn : operatorPower (n + 1) x = 1)
    (hcentral : ∀ z : B, c * z = z * c)
    (hcOrder : c * ((n + 1 : ℤ) • (1 : B)) = 1) :
    (normalizedParafermionReynoldsAddHom n x c).comp
      (normalizedParafermionReynoldsAddHom n x c) =
        normalizedParafermionReynoldsAddHom n x c := by
  ext y
  change c * parafermionReynolds (n + 1) x
      (c * parafermionReynolds (n + 1) x y) =
    c * parafermionReynolds (n + 1) x y
  have hscale : ((n + 1 : ℤ) • parafermionReynolds (n + 1) x y) =
      ((n + 1 : ℤ) • (1 : B)) * parafermionReynolds (n + 1) x y := by
    let F : AddMonoidHom B B :=
      AddMonoidHom.mk' (fun z : B => z * parafermionReynolds (n + 1) x y)
        (fun a b => add_mul a b _)
    have h := F.map_zsmul (n + 1 : ℤ) (1 : B)
    change ((n + 1 : ℤ) • (1 : B)) * parafermionReynolds (n + 1) x y =
      (n + 1 : ℤ) • (1 * parafermionReynolds (n + 1) x y) at h
    simpa only [one_mul] using h.symm
  calc
    c * parafermionReynolds (n + 1) x
        (c * parafermionReynolds (n + 1) x y) =
      c * (c * parafermionReynolds (n + 1) x
        (parafermionReynolds (n + 1) x y)) := by
          rw [parafermion_reynolds_central_left_action (n := n) (x := x)
            (c := c) (y := parafermionReynolds (n + 1) x y) (hcentral x)]
    _ = c * (c * ((n + 1 : ℤ) •
        parafermionReynolds (n + 1) x y)) := by
          rw [parafermion_reynolds_quasi_idempotent n x y hxn]
    _ = c * (c * (((n + 1 : ℤ) • (1 : B)) *
        parafermionReynolds (n + 1) x y)) := by rw [hscale]
    _ = c * parafermionReynolds (n + 1) x y := by
          calc
            c * (c * (((n + 1 : ℤ) • (1 : B)) *
                parafermionReynolds (n + 1) x y)) =
                (c * (c * ((n + 1 : ℤ) • (1 : B)))) *
                  parafermionReynolds (n + 1) x y := by noncomm_ring
            _ = c * parafermionReynolds (n + 1) x y := by
                rw [hcOrder]
                simp

/-- The normalized finite-order Reynolds operator fixes every element already
in the clock centralizer. Together with `normalized_parafermion_reynolds_comp_idempotent`,
this identifies it as a genuine retraction onto the centralizer when the
order admits the stated central normalization. -/
theorem normalized_parafermion_reynolds_fixes_centralizer (n : ℕ) (x c y : B)
    (hxn : operatorPower (n + 1) x = 1)
    (hxy : x * y = y * x)
    (hcOrder : c * ((n + 1 : ℤ) • (1 : B)) = 1) :
    normalizedParafermionReynoldsAddHom n x c y = y := by
  change c * parafermionReynolds (n + 1) x y = y
  have hraw := parafermionReynoldsRaw_commuting n x y hxy
  have hxn' : operatorPower n x * x = 1 := by
    simpa only [operatorPower] using hxn
  have hmul : x * ((n + 1 : ℤ) • (operatorPower n x * y)) =
      (n + 1 : ℤ) • (x * (operatorPower n x * y)) :=
    AddMonoidHom.map_zsmul (AddMonoidHom.mulLeft x) _ _
  have hcollapse : x * (operatorPower n x * y) = y := by
    calc
      x * (operatorPower n x * y) =
          (x * operatorPower n x) * y := by rw [mul_assoc]
      _ = (operatorPower n x * x) * y := by rw [operatorPower_commutes]
      _ = y := by rw [hxn']; simp
  calc
    c * parafermionReynolds (n + 1) x y =
        c * (x * parafermionReynoldsRaw (n + 1) x y) := rfl
    _ = c * (x * (((n + 1 : ℤ) • (operatorPower n x * y)))) := by
          rw [hraw]
    _ = c * ((n + 1 : ℤ) • y) := by
          congr 1
          rw [hmul, hcollapse]
    _ = y := by
      have hsmul : ((n + 1 : ℤ) • y) = ((n + 1 : ℤ) • (1 : B)) * y := by
        simp only [zsmul_eq_mul]
        noncomm_ring
      rw [hsmul]
      calc
        c * (((n + 1 : ℤ) • (1 : B)) * y) =
            (c * ((n + 1 : ℤ) • (1 : B))) * y := by rw [mul_assoc]
        _ = y := by rw [hcOrder, one_mul]

/-- Normalize a quasi-idempotent in an arbitrary associative ring. If `x² = a*x`
and `c` commutes with `x` and is a left inverse of `a`, then `c*x` is
idempotent. The commutation hypothesis is essential for moving the
normalizing coefficient through the averaged operator. -/
theorem normalized_quasi_idempotent (x a c : B)
    (hxx : x * x = a * x) (hcx : c * x = x * c) (hca : c * a = 1) :
    idempotencyDefect (c * x) = 0 := by
  apply sub_eq_zero.mpr
  calc
    (c * x) * (c * x) = c * (x * c) * x := by noncomm_ring
    _ = c * (c * x) * x := by rw [hcx]
    _ = (c * c) * (x * x) := by noncomm_ring
    _ = (c * c) * (a * x) := by rw [hxx]
    _ = c * (c * a) * x := by noncomm_ring
    _ = c * x := by rw [hca]; simp

/-- The order-three geometric sum is the third cyclotomic polynomial. -/
theorem operator_geometric_sum_three (x : B) :
    operatorGeometricSum 3 x = cyclo3 x := by
  simp [operatorGeometricSum, operatorPower, cyclo3]
  abel

/-- Order-four geometric factorization; factors are polynomials in one
operator, so the ambient ring need not be commutative. -/
theorem operator_geometric_sum_four (x : B) :
    operatorGeometricSum 4 x = cyclo2 x * cyclo4 x := by
  simp [operatorGeometricSum, operatorPower, cyclo2, cyclo4]
  noncomm_ring

/-- Order-six geometric factorization into the three displayed factors. -/
theorem operator_geometric_sum_six (x : B) :
    operatorGeometricSum 6 x = cyclo2 x * cyclo3 x * cyclo6 x := by
  simp [operatorGeometricSum, operatorPower, cyclo2, cyclo3, cyclo6]
  noncomm_ring

/-- Triadic scaling is the order-three cyclotomic factor followed by the
geometric sum in the third power. -/
theorem operator_geometric_sum_triadic (k : ℕ) (x : B) :
    operatorGeometricSum (3 * k) x =
      cyclo3 x * operatorGeometricSum k (x * x * x) := by
  have h := (operator_geometric_sum_composition 3 k x).1
  rw [operator_geometric_sum_three] at h
  simpa [operatorPower] using h

/-- Hexadic scaling factors the initial six terms and then sums powers of
`x^6`; this follows from multiplicative composition of finite geometric sums.
-/
theorem operator_geometric_sum_hexadic (k : ℕ) (x : B) :
    operatorGeometricSum (6 * k) x =
      cyclo2 x * cyclo3 x * cyclo6 x *
        operatorGeometricSum k (operatorPower 6 x) := by
  have h := (operator_geometric_sum_composition 6 k x).1
  rw [operator_geometric_sum_six] at h
  exact h

/-- Doubling the index factors the geometric sum into its even and odd
terms. -/
theorem operator_geometric_sum_dyadic (k : ℕ) (x : B) :
    operatorGeometricSum (2 * k) x =
      (1 + x) * operatorGeometricSum k (x * x) := by
  have hp : ∀ n : ℕ, operatorPower (2 * n) x = operatorPower n (x * x) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hidx : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
        rw [hidx, operatorPower, operatorPower, ih]
        simp only [operatorPower]
        noncomm_ring
  induction k with
  | zero => simp [operatorGeometricSum]
  | succ k ih =>
      have hidx : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [hidx, operatorGeometricSum]
      have hsplit : operatorGeometricSum (2 * k + 1) x =
          operatorGeometricSum (2 * k) x + operatorPower (2 * k) x := rfl
      rw [hsplit, ih, hp]
      simp only [operatorGeometricSum, operatorPower]
      have hterm : operatorPower (2 * k) x * x =
          x * operatorPower k (x * x) := by
        rw [← hp k]
        exact (operatorPower_commutes (2 * k) x).symm
      rw [hterm]
      noncomm_ring

/-- Vanishing of the geometric sum forces the corresponding finite-order
relation by the telescoping identity. -/
theorem operator_geometric_sum_zero_implies_power (k : ℕ) (x : B)
    (h : operatorGeometricSum k x = 0) : operatorPower k x = 1 := by
  have ht := (operator_geometric_sum_telescopes k x).1
  rw [h, mul_zero] at ht
  have heq : 1 = operatorPower k x := sub_eq_zero.mp ht.symm
  exact heq.symm

/-- A vanishing geometric sum supplies the finite-order clock relation;
combined with an operator-valued braid law, this forces the corresponding
phase power to fix the braided mode. -/
theorem geometric_sum_forces_braiding_phase_stabilization
    (n : ℕ) (x q y : B) (hsum : operatorGeometricSum n x = 0)
    (hxy : x * y = q * y * x) (hqx : x * q = q * x) :
    operatorPower n q * y = y := by
  have hx := operator_geometric_sum_zero_implies_power n x hsum
  exact finite_clock_order_forces_braiding_phase_stabilization
    n x q y hxy hqx hx

/-- A vanishing geometric sum makes `x` a finite-order element and hence
the raw parafermion Reynolds intertwiner commutes with `x`. This is a
centralizer statement; no idempotence or normalization of the sum is
asserted. -/
theorem geometric_sum_zero_gives_clock_and_reynolds_invariance
    (k : ℕ) (x y : B) (h : operatorGeometricSum k x = 0) :
    operatorPower k x = 1 ∧
    InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
      x (parafermionReynoldsRaw k x y) = 0 ∧
    InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
      x (parafermionReynolds k x y) = 0 := by
  have hpow := operator_geometric_sum_zero_implies_power k x h
  obtain ⟨hraw, hweighted⟩ := parafermion_reynolds_commutes k x y hpow
  exact ⟨hpow, hraw, hweighted⟩

/-- A root of the fourth cyclotomic polynomial squares to `-1`. Its square
is therefore an involution, while its ordinary idempotency defect is `2`;
this corrects the sometimes asserted (false over general rings) value `1`.
-/
theorem cyclo4_root_square_and_defect (x : B) (h : cyclo4 x = 0) :
    (x * x) * (x * x) = 1 ∧
    idempotencyDefect (x * x) = 1 + 1 := by
  have hsq : x * x = -1 := by
    dsimp [cyclo4] at h
    calc
      x * x = (x * x + 1) - 1 := by noncomm_ring
      _ = 0 - 1 := by rw [h]
      _ = -1 := by noncomm_ring
  constructor
  · rw [hsq]
    noncomm_ring
  · rw [hsq]
    simp only [idempotencyDefect]
    noncomm_ring

/-- Stage D80 core synthesis: all-index telescoping, the Reynolds endpoint
law, finite cyclotomic factorizations, and dyadic doubling in one
noncommutative ring. The Reynolds operator is unnormalized. -/
theorem stage_D80_all_index_operator_cyclotomic_core
    (k : ℕ) (x y : B) :
    operatorPower k x = x ^ k ∧
    operatorGeometricSum k x = ∑ i ∈ Finset.range k, x ^ i ∧
    ((1 - x) * operatorGeometricSum k x = 1 - operatorPower k x) ∧
    (operatorGeometricSum k x * (1 - x) = 1 - operatorPower k x) ∧
    (InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator
      x (parafermionReynoldsRaw k x y) =
      operatorPower k x * y - y * operatorPower k x) ∧
    (operatorGeometricSum 2 x = cyclo2 x) ∧
    (operatorGeometricSum 3 x = cyclo3 x) ∧
    (operatorGeometricSum 4 x = cyclo2 x * cyclo4 x) ∧
    (operatorGeometricSum 6 x = cyclo2 x * cyclo3 x * cyclo6 x) ∧
    (operatorGeometricSum (2 * k) x =
      (1 + x) * operatorGeometricSum k (x * x)) := by
  obtain ⟨hl, hr⟩ := operator_geometric_sum_telescopes k x
  exact ⟨operatorPower_eq_pow k x, operatorGeometricSum_eq_range_sum k x,
    hl, hr, parafermion_reynolds_raw_commutator k x y,
    by simp [operatorGeometricSum, operatorPower, cyclo2, add_comm],
    operator_geometric_sum_three x,
    operator_geometric_sum_four x, operator_geometric_sum_six x,
    operator_geometric_sum_dyadic k x⟩

/-- Stages D81–D84 in their causal order: composition of geometric windows,
square-zero cyclotomic candidates, the correctly indexed Reynolds formulas
and tetraktys selection, followed by off-shell conjugation and its
nilpotent inner-automorphism specialization. -/
theorem stages_D81_to_D84_operator_cyclotomic_synthesis
    (m k n : ℕ) (x y z u v : B)
    (hu : u * u = 0) (hv : v * v = 0) :
    (operatorGeometricSum (m * k) x =
        operatorGeometricSum m x * operatorGeometricSum k (operatorPower m x) ∧
      operatorGeometricSum (m * k) x =
        operatorGeometricSum k (operatorPower m x) * operatorGeometricSum m x) ∧
    operatorGeometricSum (3 * k) x =
      cyclo3 x * operatorGeometricSum k (x * x * x) ∧
    operatorGeometricSum (6 * k) x =
      cyclo2 x * cyclo3 x * cyclo6 x *
        operatorGeometricSum k (operatorPower 6 x) ∧
    (cyclo6 (u * v + u - v) =
        (1 - (u * v + v * u)) * (1 - (u * v + u - v)) ∧
      cyclo3 (-(u * v + u - v)) =
        (1 - (u * v + v * u)) * (1 - (u * v + u - v)) ∧
      cyclo4 (u - v) = 1 - (u * v + v * u)) ∧
    parafermionReynoldsRaw (n + 1) x 1 =
      ((n + 1 : ℤ) • operatorPower n x) ∧
    parafermionReynoldsRaw (n + 1) x (1 - x) =
      ((n + 1 : ℤ) • (operatorPower n x * (1 - x))) ∧
    (parafermionReynolds (n + 1) x 1 =
        ((n + 1 : ℤ) • operatorPower (n + 1) x) ∧
      parafermionReynolds (n + 1) x (1 - x) =
        ((n + 1 : ℤ) • (operatorPower (n + 1) x * (1 - x)))) ∧
    (parafermionReynoldsRaw 2 (isotropicDifference u v) (isotropicSum u v) = 0 ∧
      parafermionReynoldsRaw 4 (isotropicDifference u v) (isotropicSum u v) = 0 ∧
      parafermionReynoldsRaw 2 (isotropicDifference u v) (cornerUnit u v) =
        ((2 : ℤ) • (cornerUnit u v * isotropicDifference u v)) ∧
      parafermionReynoldsRaw 2 (isotropicDifference u v)
        (isotropicDifference u v) = -(2 : ℤ) • cornerUnit u v ∧
      parafermionReynoldsRaw 2 (isotropicDifference u v) (pairParity u v) = 0 ∧
      parafermionReynoldsRaw 4 (isotropicDifference u v)
        (isotropicDifference u v) =
          ((4 : ℤ) • (cornerUnit u v * cornerUnit u v)) ∧
      parafermionReynoldsRaw 4 (isotropicDifference u v) (pairParity u v) = 0) ∧
    paraUnipotentConj n z x =
      x * (1 - operatorPower n z) -
        InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator z x *
          operatorGeometricSum n z ∧
    (z ^ n = 0 →
      paraUnipotentConj n z (paraUnipotentConjInv n z x) = x ∧
      paraUnipotentConjInv n z (paraUnipotentConj n z x) = x ∧
      paraUnipotentConj n z (x * y) =
        paraUnipotentConj n z x * paraUnipotentConj n z y) := by
  have hcomp := operator_geometric_sum_composition m k x
  have hclocks := square_zero_pair_cyclotomic_candidates u v hu hv
  have hselection := isotropic_tetraktys_reynolds_mode_selection u v hu hv
  have hauto := para_unipotent_conjugation_is_inner_auto n z x y
  refine ⟨hcomp, operator_geometric_sum_triadic k x,
    operator_geometric_sum_hexadic k x, ?_,
    parafermion_reynolds_raw_one n x,
    parafermion_reynolds_raw_coboundary n x,
    parafermion_reynolds_identity_and_coboundary n x, ?_,
    para_unipotent_conjugation_off_shell n z x, ?_⟩
  · exact hclocks
  · exact hselection
  · intro hnil
    exact (hauto hnil).2

end InfoGeometry.Algebra.OperatorCyclotomicParafermions
