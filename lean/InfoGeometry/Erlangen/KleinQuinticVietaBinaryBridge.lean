/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
import InfoGeometry.Erlangen.KleinQuinticTschirnhausKleinCovariant
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Vieta Map from Ordered Roots to the Source-Ordered Binary Quintic Carrier

This module connects the ordered-root polynomial to the existing six-coordinate
binary quintic representation in the affine chart `(1,t)`. It proves the
forward evaluation identity only; it does not choose roots from coefficients
or identify the resulting five-orbit resolvent with an arbitrary quintic's
Galois resolvent.
-/

noncomputable section

namespace InfoGeometry.Erlangen.KleinQuinticVietaBinaryBridge

open InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent
open InfoGeometry.Erlangen.KleinQuinticTschirnhausKleinCovariant
open InfoGeometry.Projective.KleinQuadricPlucker
open Polynomial

/-- Ascending univariate coefficients of the monic polynomial assembled from
an ordered five-root tuple, placed in the owner's source order
`z₁^(5-j) z₂^j`. -/
def rootTupleBinaryQuintic (x : Fin 5 → ℂ) : BinaryQuinticCoefficientSpace :=
  fun j => (rootPolynomial x).coeff j.val

/-- A projective root datum uses `some r` for the finite point `[1:r]` of
`ℙ¹(ℂ)` and `none` for the point at infinity `[0:1]`. The latter is included
so polynomials of degree below five still have five projective roots, counted
with multiplicity. -/
def binaryQuinticProjectiveRoots (p : Polynomial ℂ) : Multiset (Option ℂ) :=
  p.roots.map some + Multiset.replicate (5 - p.natDegree) none

/-- The affine factor associated with a projective root: a finite root `r`
contributes `X - r`, while a root at infinity contributes the unit factor to
the affine polynomial. -/
def projectiveRootAffineFactor : Option ℂ → Polynomial ℂ
  | none => 1
  | some r => Polynomial.X - Polynomial.C r

/-- The homogeneous linear factor associated with a projective root in the
coordinates used by `binaryQuinticEval`: a finite root `[1:r]` contributes
`z₂-r z₁`, and the point at infinity `[0:1]` contributes `z₁`. -/
def projectiveRootBinaryFactor (r : Option ℂ) (z : ℂ × ℂ) : ℂ :=
  match r with
  | none => z.1
  | some a => z.2 - a * z.1

private theorem multiset_prod_map_mul_left
    (s : Multiset α) (c : ℂ) (f : α → ℂ) :
    (s.map fun a => c * f a).prod = c ^ s.card * (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp [ih, pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- Every complex polynomial of degree at most five has five projective roots
counted with multiplicity. Roots at infinity pad the affine root multiset,
and the polynomial factors by the finite roots with its leading coefficient.
This is the affine-polynomial factorization step needed before relating an
arbitrary homogeneous binary quintic to the owner's ordered-root model. -/
theorem binaryQuinticProjectiveRoots_factorization
    (p : Polynomial ℂ) (hp : p.natDegree ≤ 5) :
    (binaryQuinticProjectiveRoots p).card = 5 ∧
    p = Polynomial.C p.leadingCoeff *
      ((binaryQuinticProjectiveRoots p).map projectiveRootAffineFactor).prod := by
  have hcard : p.roots.card = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hprod :
      ((binaryQuinticProjectiveRoots p).map projectiveRootAffineFactor).prod =
        (p.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod := by
    unfold binaryQuinticProjectiveRoots
    rw [Multiset.map_add, Multiset.prod_add]
    have hfinite :
        (p.roots.map some |>.map projectiveRootAffineFactor).prod =
          (p.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod := by
      rw [Multiset.map_map]
      change (p.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod = _
      rfl
    have hinfinity :
        (Multiset.replicate (5 - p.natDegree) none |>.map
          projectiveRootAffineFactor).prod = 1 := by
      simp [projectiveRootAffineFactor]
    rw [hfinite, hinfinity, mul_one]
  constructor
  · simp only [binaryQuinticProjectiveRoots, Multiset.card_add,
      Multiset.card_map, Multiset.card_replicate]
    have := hp
    omega
  · rw [hprod]
    exact hsplit.eq_prod_roots

/-- In the owner's source order, the binary form attached to the polynomial
coefficients evaluates on the affine chart `(1,t)` as the leading coefficient
times the product over its finite roots. Projective roots at infinity are
present in `binaryQuinticProjectiveRoots` but contribute no affine factor.
This identifies coefficient evaluation with the actual projective-root
factorization, without choosing an ordering of the roots. -/
theorem binaryQuinticPolynomialCoefficients_affine_eval
    (p : Polynomial ℂ) (hp : p.natDegree ≤ 5) (t : ℂ) :
    binaryQuinticEval (fun j : Fin 6 => p.coeff j.val) (1, t) =
      p.leadingCoeff * (p.roots.map (fun r => t - r)).prod := by
  by_cases hp0 : p = 0
  · subst p
    simp [binaryQuinticEval]
  have hdegree : p.natDegree < 6 := lt_of_le_of_lt hp (by norm_num)
  have hdegree' : p.degree < 6 := by
    rw [Polynomial.degree_eq_natDegree hp0]
    exact_mod_cast hdegree
  unfold binaryQuinticEval
  simp only [one_pow, mul_one]
  calc
    (∑ j : Fin 6, p.coeff j.val * t ^ j.val) = p.eval t := by
      rw [Polynomial.eval_eq_sum]
      exact Polynomial.sum_fin (fun n a => a * t ^ n) (by intro n; simp) hdegree'
    _ = p.leadingCoeff * (p.roots.map (fun r => t - r)).prod :=
      (IsAlgClosed.splits p).eval_eq_prod_roots t

/-- The coefficient representation and the five projective factors agree at
the point at infinity. For degree five all roots are finite and the value is
the leading coefficient; for lower degree, at least one infinity factor
makes the value zero. -/
theorem binaryQuinticPolynomialCoefficients_eval_at_infinity
    (p : Polynomial ℂ) (hp : p.natDegree ≤ 5) (z₂ : ℂ) :
    binaryQuinticEval (fun j : Fin 6 => p.coeff j.val) (0, z₂) =
      p.leadingCoeff *
        ((binaryQuinticProjectiveRoots p).map
          (fun r => projectiveRootBinaryFactor r (0, z₂))).prod := by
  have hEval : binaryQuinticEval (fun j : Fin 6 => p.coeff j.val) (0, z₂) =
      p.coeff 5 * z₂ ^ 5 := by
    unfold binaryQuinticEval
    rw [Fintype.sum_eq_single (⟨5, by omega⟩ : Fin 6)]
    · simp
    · intro j hjne
      have hj5 : j.val ≠ 5 := by
        intro hj
        apply hjne
        exact Fin.ext hj
      have hexp : 5 - j.val ≠ 0 := by omega
      simp [zero_pow hexp]
  have hrootsAtInfinity :
      ((binaryQuinticProjectiveRoots p).map
        (fun r => projectiveRootBinaryFactor r (0, z₂))).prod =
          if p.natDegree = 5 then z₂ ^ 5 else 0 := by
    by_cases hd : p.natDegree = 5
    · have hcard : p.roots.card = 5 := by
        rw [IsAlgClosed.card_roots_eq_natDegree, hd]
      simp [binaryQuinticProjectiveRoots, projectiveRootBinaryFactor, hd, hcard] <;> ring
    · have hlt : p.natDegree < 5 := by
        have := hp
        omega
      have hcard : p.roots.card = p.natDegree :=
        IsAlgClosed.card_roots_eq_natDegree
      have hgap : 0 < 5 - p.natDegree := Nat.sub_pos_of_lt hlt
      simp [binaryQuinticProjectiveRoots, projectiveRootBinaryFactor,
        hlt, hcard]
      rw [if_neg hd, zero_pow (Nat.ne_of_gt hgap)]
      simp
  by_cases hd : p.natDegree = 5
  · have hcoeff : p.coeff 5 = p.leadingCoeff := by
      rw [← hd, Polynomial.coeff_natDegree]
    rw [hEval, hcoeff]
    rw [hrootsAtInfinity, if_pos hd]
  · have hlt : p.natDegree < 5 := by omega
    have hcoeff : p.coeff 5 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    rw [hEval, hcoeff]
    rw [hrootsAtInfinity, if_neg hd]
    simp

/-- Root dilation acts on the assembled quintic by dilating the polynomial
variable and multiplying by the fifth power. The hypothesis makes the
inverse substitution explicit; no coefficient scaling is being identified
with root scaling. -/
theorem rootPolynomial_scale_roots (x : Fin 5 → ℂ) (μ : ℂ) (hμ : μ ≠ 0) :
    rootPolynomial (fun i => μ * x i) =
      Polynomial.C μ ^ 5 *
        (rootPolynomial x).comp (Polynomial.C μ⁻¹ * Polynomial.X) := by
  have hfactor (i : Fin 5) :
      Polynomial.X - Polynomial.C (μ * x i) =
        Polynomial.C μ *
          (Polynomial.C μ⁻¹ * Polynomial.X - Polynomial.C (x i)) := by
    calc
      Polynomial.X - Polynomial.C (μ * x i) =
          Polynomial.C (μ * μ⁻¹) * Polynomial.X -
            Polynomial.C (μ * x i) := by
        rw [mul_inv_cancel₀ hμ]
        simp
      _ = (Polynomial.C μ * Polynomial.C μ⁻¹) * Polynomial.X -
            Polynomial.C μ * Polynomial.C (x i) := by
        rw [← Polynomial.C_mul, ← Polynomial.C_mul]
      _ = Polynomial.C μ *
          (Polynomial.C μ⁻¹ * Polynomial.X - Polynomial.C (x i)) := by ring
  change (∏ i : Fin 5,
      (Polynomial.X - Polynomial.C (μ * x i))) =
    Polynomial.C μ ^ 5 *
      (∏ i : Fin 5,
        (Polynomial.X - Polynomial.C (x i))).comp
          (Polynomial.C μ⁻¹ * Polynomial.X)
  rw [Finset.prod_congr rfl (fun i _ => hfactor i)]
  rw [Finset.prod_mul_distrib, Fin.prod_const, Polynomial.prod_comp]
  simp

/-- The source-ordered Vieta coefficients have the expected graded root
dilation weights: coefficient `j` has weight `5-j`. This is the weighted
action induced by dilating roots and differs from uniform scalar
multiplication of a coefficient vector. -/
theorem rootTupleBinaryQuintic_scale_roots
    (x : Fin 5 → ℂ) (μ : ℂ) (hμ : μ ≠ 0) (j : Fin 6) :
    rootTupleBinaryQuintic (fun i => μ * x i) j =
      μ ^ (5 - j.val) * rootTupleBinaryQuintic x j := by
  rw [rootTupleBinaryQuintic, rootTupleBinaryQuintic,
    rootPolynomial_scale_roots x μ hμ]
  rw [← Polynomial.C_pow, Polynomial.coeff_C_mul,
    Polynomial.comp_C_mul_X_coeff]
  have hj : j.val ≤ 5 := by omega
  rw [inv_pow]
  field_simp [hμ]
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hj]
  ring

/-- Homogenizing the root polynomial coefficients in the owner's convention
recovers the ordered-root polynomial on the affine chart `(1,t)`. -/
theorem rootTupleBinaryQuintic_eval (x : Fin 5 → ℂ) (t : ℂ) :
    binaryQuinticEval (rootTupleBinaryQuintic x) (1, t) =
      (rootPolynomial x).eval t := by
  have hdeg : (rootPolynomial x).natDegree < 6 := by
    rw [rootPolynomial, natDegree_finsetProd_X_sub_C_eq_card]
    simp
  rw [Polynomial.eval_eq_sum_range' hdeg]
  unfold binaryQuinticEval rootTupleBinaryQuintic
  simp only [one_pow, mul_one]
  change (∑ i : Fin 6, (rootPolynomial x).coeff i.val * t ^ i.val) = _
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (rootPolynomial x).coeff i * t ^ i)]

/-- The source-ordered binary form is homogeneous of degree five in its
projective point coordinates. -/
theorem binaryQuinticEval_commonScale (v : BinaryQuinticCoefficientSpace)
    (c : ℂ) (z : ℂ × ℂ) :
    binaryQuinticEval v (c * z.1, c * z.2) =
      c ^ 5 * binaryQuinticEval v z := by
  unfold binaryQuinticEval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hdeg : 5 - j.val + j.val = 5 := by omega
  calc
    v j * (c * z.1) ^ (5 - j.val) * (c * z.2) ^ j.val =
        c ^ 5 * (v j * z.1 ^ (5 - j.val) * z.2 ^ j.val) := by
      rw [mul_pow, mul_pow]
      calc
        v j * (c ^ (5 - j.val) * z.1 ^ (5 - j.val)) *
            (c ^ j.val * z.2 ^ j.val) =
            (c ^ (5 - j.val) * c ^ j.val) *
              (v j * z.1 ^ (5 - j.val) * z.2 ^ j.val) := by ring
        _ = c ^ 5 * (v j * z.1 ^ (5 - j.val) * z.2 ^ j.val) := by
          rw [← pow_add, hdeg]

/-- The coefficient-to-root evaluation identity extends from `(1,t)` to
every projective point in the affine chart `z₁ ≠ 0`. The factor `z₁^5` is
the degree-five homogeneous trivialization, not a coefficient-scaling law. -/
theorem binaryQuinticPolynomialCoefficients_projective_eval
    (p : Polynomial ℂ) (hp : p.natDegree ≤ 5) {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) :
    binaryQuinticEval (fun j : Fin 6 => p.coeff j.val) (z₁, z₂) =
      z₁ ^ 5 * (p.leadingCoeff *
        (p.roots.map (fun r => z₂ / z₁ - r)).prod) := by
  have hpoint : (z₁, z₂) = (z₁ * 1, z₁ * (z₂ / z₁)) := by
    congr 1
    · ring
    · field_simp [hz₁]
  rw [hpoint]
  calc
    binaryQuinticEval (fun j : Fin 6 => p.coeff j.val)
        (z₁ * 1, z₁ * (z₂ / z₁)) =
      z₁ ^ 5 * binaryQuinticEval (fun j : Fin 6 => p.coeff j.val)
        (1, z₂ / z₁) := by
          simpa using binaryQuinticEval_commonScale
            (fun j : Fin 6 => p.coeff j.val) z₁ (1, z₂ / z₁)
    _ = z₁ ^ 5 * (p.leadingCoeff *
        (p.roots.map (fun r => z₂ / z₁ - r)).prod) := by
          rw [binaryQuinticPolynomialCoefficients_affine_eval p hp]

/-- The homogeneous binary form represented by polynomial coefficients is the
product of its five projective linear root factors on all of `ℙ¹(ℂ)`. The
root multiset is unordered and includes infinity with the multiplicity needed
to pad polynomials of degree below five. -/
theorem binaryQuinticPolynomialCoefficients_projective_factorization
    (p : Polynomial ℂ) (hp : p.natDegree ≤ 5) (z : ℂ × ℂ) :
    binaryQuinticEval (fun j : Fin 6 => p.coeff j.val) z =
      p.leadingCoeff *
        ((binaryQuinticProjectiveRoots p).map
          (fun r => projectiveRootBinaryFactor r z)).prod := by
  rcases z with ⟨z₁, z₂⟩
  by_cases hz₁ : z₁ = 0
  · subst z₁
    exact binaryQuinticPolynomialCoefficients_eval_at_infinity p hp z₂
  · have hcard : (binaryQuinticProjectiveRoots p).card = 5 :=
      (binaryQuinticProjectiveRoots_factorization p hp).1
    let f : Option ℂ → ℂ := fun r =>
      match r with
      | none => 1
      | some a => z₂ / z₁ - a
    have hfactor (r : Option ℂ) :
        projectiveRootBinaryFactor r (z₁, z₂) = z₁ * f r := by
      cases r with
      | none => simp [projectiveRootBinaryFactor, f]
      | some a =>
        simp only [projectiveRootBinaryFactor, f]
        field_simp [hz₁]
    have hprod :
        ((binaryQuinticProjectiveRoots p).map
          (fun r => projectiveRootBinaryFactor r (z₁, z₂))).prod =
          z₁ ^ 5 * (p.roots.map (fun r => z₂ / z₁ - r)).prod := by
      rw [show (fun r => projectiveRootBinaryFactor r (z₁, z₂)) =
          fun r => z₁ * f r from funext hfactor]
      rw [multiset_prod_map_mul_left, hcard]
      simp [binaryQuinticProjectiveRoots, f, Multiset.map_add, Multiset.prod_add]
    rw [binaryQuinticPolynomialCoefficients_projective_eval p hp hz₁, hprod]
    ring

/-- For a binary quintic obtained from any polynomial of degree at most five,
the squared signed five-orbit coordinates are the squares of its actual
root-product evaluations on the five Klein orbit points. This composes the
projective-root factorization with the existing signed representation and
resolvent construction; the root list remains unordered. -/
theorem polynomialCoefficients_resolventTuple_eq_root_product
    (p : Polynomial ℂ) (hp : p.natDegree ≤ 5) (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (k : Fin 5) :
    binaryQuinticResolventTuple (fun j : Fin 6 => p.coeff j.val) z k =
      ((kleinOrderFiveIterate k.val z).1 ^ 5 *
        (p.leadingCoeff * (p.roots.map (fun r =>
          (kleinOrderFiveIterate k.val z).2 /
            (kleinOrderFiveIterate k.val z).1 - r)).prod)) ^ 2 := by
  unfold binaryQuinticResolventTuple binaryQuinticSignedOrbit
  rw [binaryQuinticPolynomialCoefficients_projective_eval p hp (hfirst k)]
  rw [mul_pow]
  have hsign : ((-1 : ℂ) ^ k.val) ^ 2 = 1 := by
    calc
      ((-1 : ℂ) ^ k.val) ^ 2 = (-1 : ℂ) ^ (k.val * 2) := by rw [← pow_mul]
      _ = (-1 : ℂ) ^ (2 * k.val) := by rw [Nat.mul_comm]
      _ = ((-1 : ℂ) ^ 2) ^ k.val := by rw [pow_mul]
      _ = 1 := by norm_num
  rw [hsign, one_mul]

/-- The squared five-orbit tuple for a coefficient polynomial is the square
of the product of its projective root factors at each orbit point. Unlike the
affine root-ratio formula, this statement also covers orbit points at
infinity and polynomials with roots at infinity. -/
theorem polynomialCoefficients_resolventTuple_eq_projective_root_product
    (p : Polynomial ℂ) (hp : p.natDegree ≤ 5) (z : ℂ × ℂ) (k : Fin 5) :
    binaryQuinticResolventTuple (fun j : Fin 6 => p.coeff j.val) z k =
      (p.leadingCoeff *
        ((binaryQuinticProjectiveRoots p).map (fun r =>
          projectiveRootBinaryFactor r (kleinOrderFiveIterate k.val z))).prod) ^ 2 := by
  unfold binaryQuinticResolventTuple binaryQuinticSignedOrbit
  rw [binaryQuinticPolynomialCoefficients_projective_factorization p hp
    (kleinOrderFiveIterate k.val z)]
  have hsign : ((-1 : ℂ) ^ k.val) ^ 2 = 1 := by
    calc
      ((-1 : ℂ) ^ k.val) ^ 2 = (-1 : ℂ) ^ (k.val * 2) := by rw [← pow_mul]
      _ = (-1 : ℂ) ^ (2 * k.val) := by rw [Nat.mul_comm]
      _ = ((-1 : ℂ) ^ 2) ^ k.val := by rw [pow_mul]
      _ = 1 := by norm_num
  rw [mul_pow, hsign, one_mul]

/-- The entire monic degree-five evaluation resolvent of a binary form
coming from a polynomial of degree at most five is the orbit polynomial of
the squared root-product evaluations. This is the coefficient-to-resolvent
bridge on orbit charts whose first coordinates are nonzero. -/
theorem polynomialCoefficients_evaluationResolvent_eq_root_orbit
    (p : Polynomial ℂ) (hp : p.natDegree ≤ 5) (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0) :
    binaryQuinticEvaluationResolvent (fun j : Fin 6 => p.coeff j.val) z =
      ∏ k : Fin 5,
        (Polynomial.X - Polynomial.C
          (((kleinOrderFiveIterate k.val z).1 ^ 5 *
            (p.leadingCoeff * (p.roots.map (fun r =>
              (kleinOrderFiveIterate k.val z).2 /
                (kleinOrderFiveIterate k.val z).1 - r)).prod)) ^ 2)) := by
  unfold binaryQuinticEvaluationResolvent
  apply Finset.prod_congr rfl
  intro k hk
  rw [polynomialCoefficients_resolventTuple_eq_root_product p hp z hfirst k]

/-- The coefficient-derived evaluation resolvent is the orbit polynomial of
the squared products of the five projective root factors. This version has no
chart hypothesis: each orbit point may lie at infinity, and the polynomial
may have projective roots at infinity. -/
theorem polynomialCoefficients_evaluationResolvent_eq_projective_root_orbit
    (p : Polynomial ℂ) (hp : p.natDegree ≤ 5) (z : ℂ × ℂ) :
    binaryQuinticEvaluationResolvent (fun j : Fin 6 => p.coeff j.val) z =
      ∏ k : Fin 5,
        (Polynomial.X - Polynomial.C
          ((p.leadingCoeff * ((binaryQuinticProjectiveRoots p).map (fun r =>
            projectiveRootBinaryFactor r (kleinOrderFiveIterate k.val z))).prod) ^ 2)) := by
  unfold binaryQuinticEvaluationResolvent
  apply Finset.prod_congr rfl
  intro k hk
  rw [polynomialCoefficients_resolventTuple_eq_projective_root_product p hp z k]

/-- At any point with nonzero first coordinate, the Vieta-derived binary
quintic evaluates as the homogeneous degree-five representative of the
ordered-root polynomial at the affine coordinate `z₂ / z₁`. -/
theorem rootTupleBinaryQuintic_projective_eval
    (x : Fin 5 → ℂ) {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) :
    binaryQuinticEval (rootTupleBinaryQuintic x) (z₁, z₂) =
      z₁ ^ 5 * (rootPolynomial x).eval (z₂ / z₁) := by
  have hpoint : (z₁, z₂) = (z₁ * 1, z₁ * (z₂ / z₁)) := by
    congr 1
    · ring
    · field_simp [hz₁]
  rw [hpoint]
  calc
    binaryQuinticEval (rootTupleBinaryQuintic x)
        (z₁ * 1, z₁ * (z₂ / z₁)) =
        z₁ ^ 5 * binaryQuinticEval (rootTupleBinaryQuintic x) (1, z₂ / z₁) := by
      simpa using binaryQuinticEval_commonScale
        (rootTupleBinaryQuintic x) z₁ (1, z₂ / z₁)
    _ = z₁ ^ 5 * (rootPolynomial x).eval (z₂ / z₁) := by
      rw [rootTupleBinaryQuintic_eval]

/-- The homogeneous binary quintic assembled from an ordered root tuple is
the product of its five homogeneous linear factors. Unlike the affine-chart
formula above, this identity also applies when the first projective
coordinate is zero. -/
theorem rootTupleBinaryQuintic_eval_eq_root_product
    (x : Fin 5 → ℂ) (z₁ z₂ : ℂ) :
    binaryQuinticEval (rootTupleBinaryQuintic x) (z₁, z₂) =
      ∏ i : Fin 5, (z₂ - x i * z₁) := by
  by_cases hz₁ : z₁ = 0
  · subst z₁
    have hcoeff : (rootPolynomial x).coeff 5 = 1 := by
      have hdegree : (rootPolynomial x).natDegree = 5 := by
        rw [rootPolynomial, natDegree_finsetProd_X_sub_C_eq_card]
        simp
      rw [← hdegree]
      exact (rootPolynomial_monic x).coeff_natDegree
    simp [binaryQuinticEval, rootTupleBinaryQuintic, hcoeff,
      Fin.sum_univ_succ]
  · rw [rootTupleBinaryQuintic_projective_eval x hz₁]
    have hfactor (i : Fin 5) :
        z₁ * (z₂ / z₁ - x i) = z₂ - x i * z₁ := by
      field_simp [hz₁]
    calc
      z₁ ^ 5 * (rootPolynomial x).eval (z₂ / z₁) =
          ∏ i : Fin 5, (z₁ * (z₂ / z₁ - x i)) := by
        simp only [rootPolynomial, Polynomial.eval_prod, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        simp only [Finset.card_univ, Fintype.card_fin]
      _ = ∏ i : Fin 5, (z₂ - x i * z₁) := by
        exact Finset.prod_congr rfl (fun i _ => hfactor i)

/-- The squared five-orbit coordinate of the Vieta-derived binary quintic is
the square of the root polynomial's affine value, multiplied by the degree-ten
projective trivialization factor from the orbit point's first coordinate. -/
theorem rootTupleResolventTuple_eq_polynomial_values
    (x : Fin 5 → ℂ) (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0)
    (k : Fin 5) :
    binaryQuinticResolventTuple (rootTupleBinaryQuintic x) z k =
      (kleinOrderFiveIterate k.val z).1 ^ 10 *
        (rootPolynomial x).eval
          ((kleinOrderFiveIterate k.val z).2 /
            (kleinOrderFiveIterate k.val z).1) ^ 2 := by
  simp only [binaryQuinticResolventTuple, binaryQuinticSignedOrbit]
  rw [rootTupleBinaryQuintic_projective_eval x (hfirst k)]
  have hsign : ((-1 : ℂ) ^ k.val) ^ 2 = 1 := by
    calc
      ((-1 : ℂ) ^ k.val) ^ 2 = (-1 : ℂ) ^ (k.val * 2) := by rw [← pow_mul]
      _ = (-1 : ℂ) ^ (2 * k.val) := by rw [Nat.mul_comm]
      _ = ((-1 : ℂ) ^ 2) ^ k.val := by rw [pow_mul]
      _ = 1 := by simp
  rw [mul_pow, hsign]
  ring

/-- Without any affine-chart hypothesis, a squared signed orbit coordinate
of the Vieta quintic is the square of the product of its five homogeneous
root factors at that orbit point. This includes orbit points at infinity. -/
theorem rootTupleResolventTuple_eq_homogeneous_root_values
    (x : Fin 5 → ℂ) (z : ℂ × ℂ) (k : Fin 5) :
    binaryQuinticResolventTuple (rootTupleBinaryQuintic x) z k =
      (∏ i : Fin 5,
        ((kleinOrderFiveIterate k.val z).2 -
          x i * (kleinOrderFiveIterate k.val z).1)) ^ 2 := by
  simp only [binaryQuinticResolventTuple, binaryQuinticSignedOrbit]
  rw [rootTupleBinaryQuintic_eval_eq_root_product]
  have hsign : ((-1 : ℂ) ^ k.val) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  rw [mul_pow, hsign, one_mul]

/-- The whole degree-five orbit resolvent of the Vieta-derived binary
quintic is a polynomial in homogeneous root evaluations, with no
nonvanishing-coordinate assumptions. -/
theorem rootTupleVietaEvaluationResolvent_eq_homogeneous_root_orbit
    (x : Fin 5 → ℂ) (z : ℂ × ℂ) :
    binaryQuinticEvaluationResolvent (rootTupleBinaryQuintic x) z =
      ∏ k : Fin 5, (Polynomial.X - Polynomial.C
        ((∏ i : Fin 5,
          ((kleinOrderFiveIterate k.val z).2 -
            x i * (kleinOrderFiveIterate k.val z).1)) ^ 2)) := by
  unfold binaryQuinticEvaluationResolvent
  congr 1
  funext k
  rw [rootTupleResolventTuple_eq_homogeneous_root_values]

/-- The degree-five resolvent for the binary form obtained from an ordered
root tuple is explicitly the orbit polynomial of the squared affine values of
that same root polynomial, with the projective trivialization factors kept. -/
theorem rootTupleVietaEvaluationResolvent_eq_polynomial_orbit
    (x : Fin 5 → ℂ) (z : ℂ × ℂ)
    (hfirst : ∀ k : Fin 5, (kleinOrderFiveIterate k.val z).1 ≠ 0) :
    binaryQuinticEvaluationResolvent (rootTupleBinaryQuintic x) z =
      ∏ k : Fin 5, (Polynomial.X - Polynomial.C
        ((kleinOrderFiveIterate k.val z).1 ^ 10 *
          (rootPolynomial x).eval
            ((kleinOrderFiveIterate k.val z).2 /
              (kleinOrderFiveIterate k.val z).1) ^ 2)) := by
  unfold binaryQuinticEvaluationResolvent
  congr 1
  funext k
  rw [rootTupleResolventTuple_eq_polynomial_values x z hfirst k]

/-- Reordering an ordered root tuple does not change its associated binary
quintic coefficient vector. -/
theorem rootTupleBinaryQuintic_perm (x : Fin 5 → ℂ) (σ : Equiv.Perm (Fin 5)) :
    rootTupleBinaryQuintic (fun i => x (σ i)) = rootTupleBinaryQuintic x := by
  funext j
  simp [rootTupleBinaryQuintic, rootPolynomial_perm]

/-- The multiset of roots of the polynomial assembled from a tuple is exactly
the tuple's value multiset, including multiplicities. This identifies the
fiber invariant used below without choosing an ordering of roots. -/
theorem rootPolynomial_roots_multiset (x : Fin 5 → ℂ) :
    (rootPolynomial x).roots = Finset.univ.val.map x := by
  rw [rootPolynomial, Polynomial.roots_prod]
  · simp
  · exact (rootPolynomial_monic x).ne_zero

/-- Equality of assembled root polynomials is equivalent to equality of their
root value multisets (with multiplicity). -/
theorem rootPolynomial_eq_iff_root_multiset_eq (x y : Fin 5 → ℂ) :
    rootPolynomial x = rootPolynomial y ↔
      Finset.univ.val.map x = Finset.univ.val.map y := by
  constructor
  · intro h
    have := congrArg Polynomial.roots h
    simpa only [rootPolynomial_roots_multiset] using this
  · intro h
    have hx : (rootPolynomial x).roots = (rootPolynomial y).roots := by
      rw [rootPolynomial_roots_multiset, rootPolynomial_roots_multiset, h]
    have hdegx : (rootPolynomial x).natDegree = 5 := by
      rw [rootPolynomial, natDegree_finsetProd_X_sub_C_eq_card]
      simp
    have hdegy : (rootPolynomial y).natDegree = 5 := by
      rw [rootPolynomial, natDegree_finsetProd_X_sub_C_eq_card]
      simp
    have hcardx : (rootPolynomial x).roots.card = (rootPolynomial x).natDegree := by
      rw [hdegx, rootPolynomial_roots_multiset]
      simp
    have hcardy : (rootPolynomial y).roots.card = (rootPolynomial y).natDegree := by
      rw [hdegy, rootPolynomial_roots_multiset]
      simp
    have hxpoly : rootPolynomial x =
        ((rootPolynomial x).roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
        (rootPolynomial_monic x) hcardx).symm
    have hypoly : rootPolynomial y =
        ((rootPolynomial y).roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
        (rootPolynomial_monic y) hcardy).symm
    rw [hxpoly, hypoly, hx]

/-- The six stored source-order coefficients determine the assembled monic
degree-five polynomial, and hence determine its root multiset with
multiplicity. This is the exact fiber criterion for the repository's finite
coefficient carrier. -/
theorem rootTupleBinaryQuintic_eq_iff_root_multiset_eq
    (x y : Fin 5 → ℂ) :
    rootTupleBinaryQuintic x = rootTupleBinaryQuintic y ↔
      Finset.univ.val.map x = Finset.univ.val.map y := by
  rw [← rootPolynomial_eq_iff_root_multiset_eq]
  constructor
  · intro h
    apply Polynomial.ext
    intro n
    by_cases hn : n < 6
    · have hcoeff := congrFun h ⟨n, hn⟩
      simpa [rootTupleBinaryQuintic] using hcoeff
    · have hdegx : (rootPolynomial x).natDegree = 5 := by
        rw [rootPolynomial, natDegree_finsetProd_X_sub_C_eq_card]
        simp
      have hdegy : (rootPolynomial y).natDegree = 5 := by
        rw [rootPolynomial, natDegree_finsetProd_X_sub_C_eq_card]
        simp
      rw [coeff_eq_zero_of_natDegree_lt (by omega : (rootPolynomial x).natDegree < n),
        coeff_eq_zero_of_natDegree_lt (by omega : (rootPolynomial y).natDegree < n)]
  · intro h
    funext j
    exact congrArg (fun p : Polynomial ℂ => p.coeff j.val) h

/-- Equality of the finite value multisets of two five-tuples is equivalent
to reindexing by a permutation. The `Multiset.mapEquiv` construction tracks
occurrences, so repeated roots are handled without a distinctness condition. -/
theorem root_multiset_eq_iff_reindexing (x y : Fin 5 → ℂ) :
    Finset.univ.val.map x = Finset.univ.val.map y ↔
      ∃ σ : Equiv.Perm (Fin 5), y = fun i => x (σ i) := by
  classical
  constructor
  · intro h
    let s : Multiset (Fin 5) := Finset.univ.val
    have hs : Fintype.card s = 5 := by simp [s]
    have h' : s.map x = s.map y := by simpa [s] using h
    let idx : Fin 5 ≃ s := {
      toFun := fun i => ⟨i, ⟨0, by simp [s]⟩⟩
      invFun := fun i => i.1
      left_inv := by intro i; rfl
      right_inv := by
        intro a
        rcases a with ⟨i, ⟨k, hk⟩⟩
        have hcount : s.count i = 1 := by simp [s]
        have hk0 : k = 0 := by rw [hcount] at hk; omega
        subst k
        rfl }
    let e : s ≃ s :=
      (s.mapEquiv x).trans ((Equiv.cast (congrArg Multiset.ToType h')).trans
        (s.mapEquiv y).symm)
    let σ : Equiv.Perm (Fin 5) := idx.trans (e.symm.trans idx.symm)
    have cast_fst (m n : Multiset ℂ) (hmn : m = n) (a : m) :
        (cast (congrArg Multiset.ToType hmn) a).1 = a.1 := by
      cases hmn
      rfl
    have heval (i : s) : x i.1 = y (e i).1 := by
      have hmap : s.mapEquiv y (e i) =
          Equiv.cast (congrArg Multiset.ToType h') (s.mapEquiv x i) := by
        simp [e]
      have hv := congrArg (fun z : s.map y => z.1) hmap
      have hvcast := cast_fst (s.map x) (s.map y) h' (s.mapEquiv x i)
      have hv' := hv.trans hvcast
      simpa only [Multiset.mapEquiv_apply] using hv'.symm
    refine ⟨σ, ?_⟩
    funext i
    have hσ : idx (σ i) = e.symm (idx i) := by simp [σ]
    have htarget : e (idx (σ i)) = idx i := by rw [hσ]; simp
    have hv := (heval (idx (σ i))).symm
    rw [htarget] at hv
    dsimp [idx] at hv
    exact hv
  · rintro ⟨σ, rfl⟩
    exact (rootPolynomial_eq_iff_root_multiset_eq x
      (fun i => x (σ i))).mp (rootPolynomial_perm x σ).symm

/-- The repository's six-coordinate binary-quintic coefficient fiber is
exactly the `S₅` reindexing orbit of the ordered root tuple. -/
theorem rootTupleBinaryQuintic_eq_iff_reindexing
    (x y : Fin 5 → ℂ) :
    rootTupleBinaryQuintic x = rootTupleBinaryQuintic y ↔
      ∃ σ : Equiv.Perm (Fin 5), y = fun i => x (σ i) := by
  rw [rootTupleBinaryQuintic_eq_iff_root_multiset_eq,
    root_multiset_eq_iff_reindexing]

/-- Equality of the squared evaluation resolvent with Klein's Brioschi orbit
polynomial determines the five roots as a multiset, including multiplicity.
Equivalently, their indexed tuples differ only by a permutation. No
distinct-root assumption or canonical ordering is used. -/
theorem binaryQuinticEvaluationResolvent_eq_kleinBrioschiOrbitPolynomial_iff_reindexing
    (v : BinaryQuinticCoefficientSpace) (z : ℂ × ℂ) :
    binaryQuinticEvaluationResolvent v z = kleinBrioschiOrbitPolynomial z ↔
      ∃ σ : Equiv.Perm (Fin 5),
        kleinBrioschiRootTuple z =
          fun i => binaryQuinticResolventTuple v z (σ i) := by
  constructor
  · intro h
    have hpoly :
        rootPolynomial (binaryQuinticResolventTuple v z) =
          rootPolynomial (kleinBrioschiRootTuple z) := by
      simpa [binaryQuinticEvaluationResolvent, rootPolynomial,
        kleinBrioschiOrbitPolynomial] using h
    have hmultiset :=
      (rootPolynomial_eq_iff_root_multiset_eq
        (binaryQuinticResolventTuple v z) (kleinBrioschiRootTuple z)).mp hpoly
    exact (root_multiset_eq_iff_reindexing
      (binaryQuinticResolventTuple v z) (kleinBrioschiRootTuple z)).mp hmultiset
  · rintro ⟨σ, hσ⟩
    have hpoly :
        rootPolynomial (kleinBrioschiRootTuple z) =
          rootPolynomial (binaryQuinticResolventTuple v z) := by
      rw [hσ, rootPolynomial_perm]
    simpa [binaryQuinticEvaluationResolvent, rootPolynomial,
      kleinBrioschiOrbitPolynomial] using hpoly.symm

/-- The image of the actual ordered-root coefficient map. This is the
root-assembled locus inside the six-coordinate coefficient carrier, not a
claim that every binary quintic has been represented by affine roots. -/
abbrev RootTupleBinaryQuinticImage := Set.range rootTupleBinaryQuintic

/-- The resolvent obtained by first forming the Vieta polynomial and then
applying the existing binary-quintic construction is independent of the
ordering chosen for the five roots. This is forward permutation descent; it
does not select an ordering from an arbitrary coefficient vector. -/
theorem rootTupleVietaEvaluationResolvent_perm
    (x : Fin 5 → ℂ) (σ : Equiv.Perm (Fin 5)) (z : ℂ × ℂ) :
    binaryQuinticEvaluationResolvent
        (rootTupleBinaryQuintic (fun i => x (σ i))) z =
      binaryQuinticEvaluationResolvent (rootTupleBinaryQuintic x) z := by
  rw [rootTupleBinaryQuintic_perm]

/-- A concrete ordered-root witness for the distinction between the
coefficient quotient and the ordered Klein covariant: swapping the first two
roots leaves the Vieta binary-quintic coefficient vector fixed, while the
ambient ten-coordinate bivector changes. Thus the covariant is equivariant
upstairs, but cannot be a function of the unordered coefficient vector alone. -/
theorem same_vieta_coefficients_different_ordered_klein_covariant :
    rootTupleBinaryQuintic
        (fun i : Fin 5 => ((Equiv.swap (0 : Fin 5) 1 i).val : ℂ)) =
      rootTupleBinaryQuintic (fun i => (i.val : ℂ)) ∧
    rootKleinOmega5
        (fun i : Fin 5 => ((Equiv.swap (0 : Fin 5) 1 i).val : ℂ)) ≠
      rootKleinOmega5 (fun i => (i.val : ℂ)) := by
  constructor
  · exact rootTupleBinaryQuintic_perm (fun i => (i.val : ℂ)) (Equiv.swap 0 1)
  · intro h
    have hcoord := congrFun h ⟨(0, 2), by decide⟩
    norm_num [rootKleinOmega5, centeredRoots, centeredRootSquares, rootMean,
      Equiv.swap_apply_def, Fin.sum_univ_succ] at hcoord

/-- The ambient ordered-root Klein covariant cannot be recovered by any
function of the Vieta coefficient vector alone. The witness is the first-two
root transposition: it fixes the coefficient vector and changes an ambient
Plücker coordinate. This rules out a coefficient-space factorization of
this particular covariant; it does not rule out invariant constructions
such as the squared-orbit resolvent. -/
theorem rootKleinOmega5_does_not_factor_through_vieta :
    ¬ ∃ F : BinaryQuinticCoefficientSpace → RootPair5 → ℂ,
      ∀ x p, F (rootTupleBinaryQuintic x) p = rootKleinOmega5 x p := by
  rintro ⟨F, hF⟩
  obtain ⟨hcoeff, hcov⟩ :=
    same_vieta_coefficients_different_ordered_klein_covariant
  apply hcov
  funext p
  rw [← hF (fun i : Fin 5 => ((Equiv.swap (0 : Fin 5) 1 i).val : ℂ)) p,
    ← hF (fun i : Fin 5 => (i.val : ℂ)) p, hcoeff]

/-- The six-coordinate Klein-quadric covariant also fails to factor through
the unordered Vieta coefficient vector. This witness concerns precisely the
`Gr(2,4)` chart `rootKleinOmega`, rather than only its ten-coordinate
five-dimensional ambient representative. -/
theorem same_vieta_coefficients_different_six_coordinate_klein_covariant :
    rootTupleBinaryQuintic
        (fun i : Fin 5 => ((Equiv.swap (0 : Fin 5) 1 i).val : ℂ)) =
      rootTupleBinaryQuintic (fun i => (i.val : ℂ)) ∧
    rootKleinOmega
        (fun i : Fin 5 => ((Equiv.swap (0 : Fin 5) 1 i).val : ℂ)) ≠
      rootKleinOmega (fun i => (i.val : ℂ)) := by
  constructor
  · exact rootTupleBinaryQuintic_perm (fun i => (i.val : ℂ)) (Equiv.swap 0 1)
  · intro h
    have hcoord := congrArg Plucker6.p01 h
    norm_num [rootKleinOmega, standardCoordinates, centeredRoots,
      centeredRootSquares, rootMean, Plucker6.pluckerLine,
      Equiv.swap_apply_def,
      Fin.sum_univ_succ] at hcoord

/-- No function of the coefficient vector alone recovers the six-coordinate
ordered-root Klein covariant. The root permutation acts covariantly on its
Grassmann chart, while Vieta forgets that ordering. -/
theorem rootKleinOmega_does_not_factor_through_vieta :
    ¬ ∃ F : BinaryQuinticCoefficientSpace → Plucker6 ℂ,
      ∀ x, F (rootTupleBinaryQuintic x) = rootKleinOmega x := by
  rintro ⟨F, hF⟩
  obtain ⟨hcoeff, hcov⟩ :=
    same_vieta_coefficients_different_six_coordinate_klein_covariant
  apply hcov
  rw [← hF (fun i : Fin 5 => ((Equiv.swap (0 : Fin 5) 1 i).val : ℂ)),
    ← hF (fun i : Fin 5 => (i.val : ℂ)), hcoeff]

/-- The set-valued Klein datum over an ordered root tuple: retain every
six-coordinate point obtained by permuting its roots. This is the fiberwise
orbit object appropriate to the Vieta quotient; it does not choose a point
from the orbit. -/
def rootKleinPermutationOrbit (x : Fin 5 → ℂ) : Set (Plucker6 ℂ) :=
  {P | ∃ σ : Equiv.Perm (Fin 5),
    rootKleinOmega (fun i => x (σ i)) = P}

/-- The orbit-valued Klein datum is unchanged when the ordered roots are
reindexed. -/
theorem rootKleinPermutationOrbit_perm (x : Fin 5 → ℂ)
    (τ : Equiv.Perm (Fin 5)) :
    rootKleinPermutationOrbit (fun i => x (τ i)) =
      rootKleinPermutationOrbit x := by
  ext P
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ.trans τ, ?_⟩
    simpa [Equiv.trans_apply] using hσ
  · rintro ⟨σ, hσ⟩
    refine ⟨σ.trans τ.symm, ?_⟩
    simpa [Equiv.trans_apply] using hσ

/-- Every point in the orbit-valued datum remains on Klein's quadric. -/
theorem rootKleinPermutationOrbit_on_klein (x : Fin 5 → ℂ)
    (P : Plucker6 ℂ) (hP : P ∈ rootKleinPermutationOrbit x) :
    Plucker6.kleinQ P = 0 := by
  rcases hP with ⟨σ, rfl⟩
  exact rootKleinOmega_on_klein (fun i => x (σ i))

/-- The Vieta–Klein roof on ordered affine root tuples. Its coefficient
component is single-valued and S₅-invariant; its Grassmann component is the
full Klein orbit above that coefficient datum. -/
def rootVietaKleinRoof (x : Fin 5 → ℂ) :
    BinaryQuinticCoefficientSpace × Set (Plucker6 ℂ) :=
  (rootTupleBinaryQuintic x, rootKleinPermutationOrbit x)

/-- The Vieta–Klein roof is invariant under root reordering, so it is
well-defined on the orbit quotient even though no single Klein point is. -/
theorem rootVietaKleinRoof_perm (x : Fin 5 → ℂ)
    (σ : Equiv.Perm (Fin 5)) :
    rootVietaKleinRoof (fun i => x (σ i)) = rootVietaKleinRoof x := by
  simp [rootVietaKleinRoof, rootTupleBinaryQuintic_perm,
    rootKleinPermutationOrbit_perm]

/-- Reindexing equivalence on ordered root tuples. This is the explicit
finite `S₅` orbit relation used for the root-side quotient. -/
def rootReindexingSetoid : Setoid (Fin 5 → ℂ) where
  r x y := ∃ σ : Equiv.Perm (Fin 5), y = fun i => x (σ i)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨Equiv.refl _, rfl⟩
    · intro x y hxy
      rcases hxy with ⟨σ, rfl⟩
      refine ⟨σ.symm, ?_⟩
      funext i
      simp
    · intro x y z hxy hyz
      rcases hxy with ⟨σ, rfl⟩
      rcases hyz with ⟨τ, rfl⟩
      refine ⟨τ.trans σ, ?_⟩
      funext i
      rfl

/-- The coefficient fiber relation on ordered tuples is exactly the
root-reindexing relation. -/
theorem rootReindexingSetoid_iff_vieta_eq (x y : Fin 5 → ℂ) :
    rootReindexingSetoid.r x y ↔
      rootTupleBinaryQuintic x = rootTupleBinaryQuintic y := by
  change (∃ σ : Equiv.Perm (Fin 5), y = fun i => x (σ i)) ↔ _
  exact (rootTupleBinaryQuintic_eq_iff_reindexing x y).symm

/-- The coefficient map descends to the root-reindexing quotient. -/
noncomputable def rootQuotientToVietaImage :
    Quotient rootReindexingSetoid → RootTupleBinaryQuinticImage :=
  Quotient.lift
    (fun x => (⟨rootTupleBinaryQuintic x, ⟨x, rfl⟩⟩ : RootTupleBinaryQuinticImage))
    (by
      intro x y hxy
      apply Subtype.ext
      exact (rootReindexingSetoid_iff_vieta_eq x y).mp hxy)

@[simp] theorem rootQuotientToVietaImage_mk (x : Fin 5 → ℂ) :
    rootQuotientToVietaImage (Quotient.mk rootReindexingSetoid x) =
      ⟨rootTupleBinaryQuintic x, ⟨x, rfl⟩⟩ := rfl

/-- The descended coefficient map is bijective: its fibers are precisely
the `S₅` reindexing classes. -/
theorem rootQuotientToVietaImage_bijective :
    Function.Bijective rootQuotientToVietaImage := by
  constructor
  · intro q r hqr
    revert hqr
    refine Quotient.inductionOn₂ q r ?_
    intro x y hxy
    apply Quotient.sound
    apply (rootReindexingSetoid_iff_vieta_eq x y).mpr
    exact congrArg Subtype.val hxy
  · rintro ⟨c, ⟨x, rfl⟩⟩
    exact ⟨Quotient.mk rootReindexingSetoid x, rfl⟩

/-- Equivalence between the ordered-root `S₅` quotient and the image of its
source-ordered binary-quintic coefficient representation. -/
noncomputable def rootReindexingQuotientEquivVietaImage :
    Quotient rootReindexingSetoid ≃ RootTupleBinaryQuinticImage :=
  Equiv.ofBijective rootQuotientToVietaImage rootQuotientToVietaImage_bijective

/-- Respect of the root-side roof under the reindexing relation. -/
theorem rootVietaKleinRoof_respects_reindexing
    (x y : Fin 5 → ℂ)
    (hxy : rootReindexingSetoid.r x y) :
    rootVietaKleinRoof x = rootVietaKleinRoof y := by
  rcases hxy with ⟨σ, rfl⟩
  exact (rootVietaKleinRoof_perm x σ).symm

/-- The orbit-valued Vieta–Klein roof descends to the quotient of ordered
root tuples by reindexing. This quotient is the `S₅` orbit quotient of the
root carrier; no identification with an independently presented coefficient
space quotient is assumed. -/
noncomputable def rootVietaKleinRoofOnReindexingQuotient :
    Quotient rootReindexingSetoid →
      BinaryQuinticCoefficientSpace × Set (Plucker6 ℂ) :=
  Quotient.lift rootVietaKleinRoof rootVietaKleinRoof_respects_reindexing

/-- On the root-assembled coefficient image, the coefficient projection of
the descended Vieta–Klein roof is exactly the quotient-to-image map. This
identifies the roof with the actual finite coefficient fibers and keeps the
Klein component set-valued over an `S₅`-orbit. -/
theorem rootVietaKleinRoofOnReindexingQuotient_fst
    (q : Quotient rootReindexingSetoid) :
    (rootVietaKleinRoofOnReindexingQuotient q).1 =
      (rootQuotientToVietaImage q).val := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- Every Klein point in the quotient roof is decomposable on the Klein
quadric. This is a statement over the finite image of the affine root
coefficient map, with no chosen inverse to Vieta. -/
theorem rootVietaKleinRoofOnReindexingQuotient_on_klein
    (q : Quotient rootReindexingSetoid) (P : Plucker6 ℂ)
    (hP : P ∈ (rootVietaKleinRoofOnReindexingQuotient q).2) :
    Plucker6.kleinQ P = 0 := by
  revert hP
  refine Quotient.inductionOn q ?_
  intro x hP
  change P ∈ rootKleinPermutationOrbit x at hP
  exact rootKleinPermutationOrbit_on_klein x P hP

@[simp] theorem rootVietaKleinRoofOnReindexingQuotient_mk
    (x : Fin 5 → ℂ) :
    rootVietaKleinRoofOnReindexingQuotient
      (Quotient.mk rootReindexingSetoid x) = rootVietaKleinRoof x := rfl

end InfoGeometry.Erlangen.KleinQuinticVietaBinaryBridge
