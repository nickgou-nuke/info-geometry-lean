/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ChiralZornCARAndSchurBridge
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Transport of algebraic CAR relations

This file records the precise algebraic interface behind transport of a CAR
relation.  No physical interpretation is part of the theorem: the map is
only required to preserve addition, multiplication, and the unit.
-/

namespace InfoGeometry.Algebra.ChiralCARTransport

variable {A : Type*} [Ring A]
variable {B : Type*} [Ring B]

/-- A one-mode algebraic CAR packet.  This is a relation-level model, not a
physical interpretation: the carrier is any associative ring with unit. -/
structure OneModeCAR (A : Type*) [Ring A] where
  annihilator : A
  creator : A
  annihilator_sq : annihilator * annihilator = 0
  creator_sq : creator * creator = 0
  anticommutator_one :
    annihilator * creator + creator * annihilator = 1

theorem map_anticommutator_eq_of_preserving
    (U : A → A)
    (hAdd : ∀ x y, U (x + y) = U x + U y)
    (hMul : ∀ x y, U (x * y) = U x * U y)
    (hOne : U 1 = 1)
    {p q : A}
    (hCAR : p * q + q * p = 1) :
    U p * U q + U q * U p = 1 := by
  rw [← hMul p q, ← hMul q p, ← hAdd, hCAR, hOne]

theorem map_square_zero_of_preserving
    (U : A → A)
    (hMul : ∀ x y, U (x * y) = U x * U y)
    (hZero : U 0 = 0)
    {p : A}
    (hp : p * p = 0) :
    U p * U p = 0 := by
  rw [← hMul p p, hp]
  exact hZero

/-- A ring equivalence preserves the normalized one-mode CAR relation. -/
theorem ringEquiv_map_CAR
    (U : A ≃+* A) {p q : A}
    (hCAR : p * q + q * p = 1) :
    U p * U q + U q * U p = 1 := by
  rw [← U.map_mul, ← U.map_mul, ← U.map_add, hCAR, U.map_one]

/-- The CAR relation is reflected as well as preserved by a ring equivalence. -/
theorem ringEquiv_map_CAR_iff
    (U : A ≃+* B) {p q : A} :
    (U p * U q + U q * U p = 1) ↔ p * q + q * p = 1 := by
  constructor
  · intro h
    have h' := congrArg U.symm h
    simpa only [map_mul, map_add, map_one, U.symm_apply_apply] using h'
  · exact fun h => by
      rw [← U.map_mul, ← U.map_mul, ← U.map_add, h, U.map_one]

/-- A ring equivalence transports the complete one-mode CAR packet. -/
def OneModeCAR.map (U : A ≃+* B) (C : OneModeCAR A) : OneModeCAR B where
  annihilator := U C.annihilator
  creator := U C.creator
  annihilator_sq := by
    rw [← U.map_mul, C.annihilator_sq, U.map_zero]
  creator_sq := by
    rw [← U.map_mul, C.creator_sq, U.map_zero]
  anticommutator_one := by
    rw [← U.map_mul, ← U.map_mul, ← U.map_add,
      C.anticommutator_one, U.map_one]

/-- Transport through an equivalence and its inverse returns the original CAR
packet, including its distinguished generators. -/
theorem OneModeCAR.map_symm_map (U : A ≃+* B) (C : OneModeCAR A) :
    OneModeCAR.map U.symm (OneModeCAR.map U C) = C := by
  cases C with
  | mk annihilator creator annihilator_sq creator_sq anticommutator_one =>
    simp only [OneModeCAR.map]
    congr
    · exact U.symm_apply_apply annihilator
    · exact U.symm_apply_apply creator

theorem OneModeCAR.map_map_symm (U : A ≃+* B) (D : OneModeCAR B) :
    OneModeCAR.map U (OneModeCAR.map U.symm D) = D := by
  cases D with
  | mk annihilator creator annihilator_sq creator_sq anticommutator_one =>
    simp only [OneModeCAR.map]
    congr
    · exact U.apply_symm_apply annihilator
    · exact U.apply_symm_apply creator

/-- Transport through an equivalence preserves the complete CAR packet in both
directions. -/
theorem OneModeCAR.map_iff (U : A ≃+* B) (C : OneModeCAR A) (D : OneModeCAR B) :
    D = OneModeCAR.map U C ↔ OneModeCAR.map U.symm D = C := by
  constructor
  · intro h
    rw [h, OneModeCAR.map_symm_map]
  · intro h
    have h' := congrArg (OneModeCAR.map U) h
    rw [OneModeCAR.map_map_symm] at h'
    exact h'

section LinearMixing

variable {R : Type*} [CommRing R] [Algebra R A]

/-- Linear mixing of square-zero operators is controlled by their
anticommutator, without any commutativity assumption on the operators. -/
theorem linear_mix_square (u v : R) (p q : A)
    (hp : p * p = 0) (hq : q * q = 0) :
    (u • p + v • q) * (u • p + v • q) =
      (u * v) • (p * q + q * p) := by
  simp only [add_mul, mul_add, smul_mul_smul, hp, hq, smul_zero,
    zero_add, add_zero, smul_add]
  rw [mul_comm v u, add_comm]

/-- A normalized CAR pair gives the exact square of every linear mixture.
In particular a balanced mixture is not another square-zero CAR generator. -/
theorem linear_mix_square_of_CAR (u v : R) (p q : A)
    (hp : p * p = 0) (hq : q * q = 0) (hCAR : p * q + q * p = 1) :
    (u • p + v • q) * (u • p + v • q) = (u * v) • (1 : A) := by
  rw [linear_mix_square u v p q hp hq, hCAR]

/-- The mixed CAR relation transforms by the polarized coefficient form. -/
theorem linear_mix_anticommutator (u v s t : R) (p q : A)
    (hp : p * p = 0) (hq : q * q = 0) :
    (u • p + v • q) * (s • p + t • q) +
      (s • p + t • q) * (u • p + v • q) =
      (u * t + v * s) • (p * q + q * p) := by
  simp only [add_mul, mul_add, smul_mul_smul, hp, hq, smul_zero,
    zero_add, add_zero, smul_add, add_smul]
  rw [mul_comm s v, mul_comm t u]
  abel

end LinearMixing

/-- Over a field, a one-mode CAR mixture is square-zero precisely on one
of its two coefficient axes. The ambient algebra remains noncommutative. -/
theorem linear_mix_square_zero_iff
    {K : Type*} [Field K] [Algebra K A] [Nontrivial A]
    (u v : K) (p q : A)
    (hp : p * p = 0) (hq : q * q = 0) (hCAR : p * q + q * p = 1) :
    (u • p + v • q) * (u • p + v • q) = 0 ↔ u = 0 ∨ v = 0 := by
  rw [linear_mix_square_of_CAR u v p q hp hq hCAR]
  simp only [smul_eq_zero, one_ne_zero, or_false, mul_eq_zero]

/-- Exact preservation criterion for both square-zero relations and the
normalized anticommutator. This is a statement in the full operator algebra,
not a claim that an arbitrary coefficient rotation preserves CAR. -/
theorem linear_mix_CAR_iff
    {K : Type*} [Field K] [Algebra K A] [Nontrivial A]
    (u v s t : K) (p q : A)
    (hp : p * p = 0) (hq : q * q = 0) (hCAR : p * q + q * p = 1) :
    ((u • p + v • q) * (u • p + v • q) = 0 ∧
      (s • p + t • q) * (s • p + t • q) = 0 ∧
      (u • p + v • q) * (s • p + t • q) +
        (s • p + t • q) * (u • p + v • q) = 1) ↔
      (u = 0 ∨ v = 0) ∧ (s = 0 ∨ t = 0) ∧ u * t + v * s = 1 := by
  rw [linear_mix_square_zero_iff u v p q hp hq hCAR,
    linear_mix_square_zero_iff s t p q hp hq hCAR,
    linear_mix_anticommutator u v s t p q hp hq, hCAR]
  have hcoeff : (u * t + v * s) • (1 : A) = 1 ↔ u * t + v * s = 1 := by
    simpa only [one_smul] using
      (smul_left_inj (R := K) (one_ne_zero : (1 : A) ≠ 0) :
        (u * t + v * s) • (1 : A) = (1 : K) • (1 : A) ↔
          u * t + v * s = 1)
  rw [hcoeff]

/-- The action of a quadratic operator is determined by two anticommutators. -/
theorem quadratic_commutator (a b x : A) :
    (a * b) * x - x * (a * b) =
      a * (b * x + x * b) - (a * x + x * a) * b := by
  noncomm_ring

/-- The number-preserving cross-current cannot generate particle--hole
mixing of its first square-zero factor. -/
theorem cross_current_commutes_left (p q : A)
    (hp : p * p = 0) (hpq : p * q + q * p = 0) :
    (p * q - q * p) * p - p * (p * q - q * p) = 0 := by
  have hqp : q * p + p * q = 0 := by simpa only [add_comm] using hpq
  calc
    _ = ((p * q) * p - p * (p * q)) -
        ((q * p) * p - p * (q * p)) := by noncomm_ring
    _ = 0 := by
      rw [quadratic_commutator, quadratic_commutator, hp, hqp]
      simp

/-- Pair annihilation minus pair creation sends the first annihilator to
its partner creator. Only the relations used by this action are assumed. -/
theorem pairing_current_commutator_annihilator
    (p P q Q : A) (hp : p * p = 0)
    (hqp : q * p + p * q = 0) (hQp : Q * p + p * Q = 0)
    (hPp : P * p + p * P = 1) :
    (q * p - P * Q) * p - p * (q * p - P * Q) = Q := by
  calc
    _ = ((q * p) * p - p * (q * p)) -
        ((P * Q) * p - p * (P * Q)) := by noncomm_ring
    _ = Q := by
      rw [quadratic_commutator, quadratic_commutator, hp, hqp, hQp, hPp]
      simp

/-- The same pairing current sends the partner creator to minus the first
annihilator, giving the infinitesimal circular mixing plane. -/
theorem pairing_current_commutator_creator
    (p P q Q : A) (hQ : Q * Q = 0)
    (hpQ : p * Q + Q * p = 0) (hPQ : P * Q + Q * P = 0)
    (hqQ : q * Q + Q * q = 1) :
    (q * p - P * Q) * Q - Q * (q * p - P * Q) = -p := by
  calc
    _ = ((q * p) * Q - Q * (q * p)) -
        ((P * Q) * Q - Q * (P * Q)) := by noncomm_ring
    _ = -p := by
      rw [quadratic_commutator, quadratic_commutator, hQ, hpQ, hPQ, hqQ]
      simp

/-- Explicit star-duality makes the circular pairing current skew-adjoint;
CAR relations alone do not supply this star statement. -/
theorem pairing_current_star [StarRing A] (p P q Q : A)
    (hP : P = star p) (hQ : Q = star q) :
    star (q * p - P * Q) = -(q * p - P * Q) := by
  subst P
  subst Q
  simp only [star_sub, star_mul, star_star]
  abel

/-- Exact defect of a circular eigenoperator. The coefficient `r` is a
square root of minus one; the operators need not commute. -/
theorem circular_commutator_defect
    {R : Type*} [CommRing R] [Algebra R A]
    (r : R) (hr : r * r = -1) (G x y : A) :
    G * (x + r • y) - (x + r • y) * G - (-r) • (x + r • y) =
      (G * x - x * G - y) + r • (G * y - y * G + x) := by
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_sub, smul_smul, neg_mul, hr, neg_neg, one_smul, neg_smul]
  abel

/-- A circular commutator plane diagonalizes over any central scalar ring
containing a square root of minus one. Replacing `r` by `-r` gives the opposite
weight. This is an operator identity, with no assertion of linear independence. -/
theorem circular_commutator_eigenoperator
    {R : Type*} [CommRing R] [Algebra R A]
    (r : R) (hr : r * r = -1) (G x y : A)
    (hx : G * x - x * G = y) (hy : G * y - y * G = -x) :
    G * (x + r • y) - (x + r • y) * G = (-r) • (x + r • y) := by
  apply sub_eq_zero.mp
  rw [circular_commutator_defect r hr, hx, hy]
  simp

/-- The coefficients of a normalized CAR pair are recovered by taking
anticommutators with its two generators. -/
theorem linear_mix_eq_zero_iff
    {K : Type*} [Field K] [Algebra K A] [Nontrivial A]
    (u v : K) (p q : A)
    (hp : p * p = 0) (hq : q * q = 0) (hCAR : p * q + q * p = 1) :
    u • p + v • q = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hu := linear_mix_anticommutator u v 0 1 p q hp hq
    have hv := linear_mix_anticommutator u v 1 0 p q hp hq
    rw [h, hCAR] at hu hv
    have hu0 : u • (1 : A) = 0 := by simpa using hu.symm
    have hv0 : v • (1 : A) = 0 := by simpa using hv.symm
    exact ⟨(smul_eq_zero.mp hu0).resolve_right one_ne_zero,
      (smul_eq_zero.mp hv0).resolve_right one_ne_zero⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- A normalized square-zero CAR pair is linearly independent over its
scalar field, without a finite-dimensional or matrix-coordinate assumption. -/
theorem CAR_pair_linearIndependent
    {K : Type*} [Field K] [Algebra K A] [Nontrivial A]
    (p q : A) (hp : p * p = 0) (hq : q * q = 0)
    (hCAR : p * q + q * p = 1) :
    LinearIndependent K ![p, q] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := (linear_mix_eq_zero_iff (g 0) (g 1) p q hp hq hCAR).mp
    (by simpa [Fin.sum_univ_two] using hg)
  fin_cases i
  · exact h.1
  · exact h.2

/-- The split Clifford combinations of a CAR pair are independent when two
is nonzero. Without that scalar condition they coincide. -/
theorem CAR_split_pair_linearIndependent
    {K : Type*} [Field K] [Algebra K A] [Nontrivial A]
    (h2 : (2 : K) ≠ 0) (p q : A) (hp : p * p = 0) (hq : q * q = 0)
    (hCAR : p * q + q * p = 1) :
    LinearIndependent K ![p + q, p - q] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hz : (g 0 + g 1) • p + (g 0 - g 1) • q = 0 := by
    have hg' : g 0 • (p + q) + g 1 • (p - q) = 0 := by
      simpa [Fin.sum_univ_two] using hg
    rw [smul_add, smul_sub] at hg'
    simpa only [add_smul, sub_smul] using (show
      g 0 • p + g 1 • p + (g 0 • q - g 1 • q) = 0 by
        calc _ = g 0 • p + g 0 • q + (g 1 • p - g 1 • q) := by abel
             _ = 0 := hg')
  obtain ⟨hu, hv⟩ := (linear_mix_eq_zero_iff _ _ p q hp hq hCAR).mp hz
  have h0 : (2 : K) * g 0 = 0 := by linear_combination hu + hv
  have h1 : (2 : K) * g 1 = 0 := by linear_combination hu - hv
  fin_cases i
  · exact (mul_eq_zero.mp h0).resolve_left h2
  · exact (mul_eq_zero.mp h1).resolve_left h2

/-- Exact scalar obstruction to the split Clifford pair being a basis of
its two-generator span: characteristic two collapses the two combinations. -/
theorem CAR_split_pair_linearIndependent_iff
    {K : Type*} [Field K] [Algebra K A] [Nontrivial A]
    (p q : A) (hp : p * p = 0) (hq : q * q = 0)
    (hCAR : p * q + q * p = 1) :
    LinearIndependent K ![p + q, p - q] ↔ (2 : K) ≠ 0 := by
  constructor
  · intro h h2
    have hqq : q + q = 0 := by
      have h := congrArg (fun c : K => c • q) h2
      simpa only [two_smul K q, zero_smul] using h
    have heq : p + q = p - q := by
      calc p + q = (p - q) + (q + q) := by abel
           _ = p - q := by rw [hqq, add_zero]
    have h01 : (0 : Fin 2) = 1 := h.injective (by simpa using heq)
    exact Fin.zero_ne_one h01
  · intro h2
    exact CAR_split_pair_linearIndependent h2 p q hp hq hCAR

end InfoGeometry.Algebra.ChiralCARTransport
