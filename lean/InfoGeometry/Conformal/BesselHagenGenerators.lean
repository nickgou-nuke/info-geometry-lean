/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Conformal.BesselHagenCurrent
import InfoGeometry.Conformal.MaxwellStressTensor
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The real translation, Lorentz, dilation and special-conformal currents

Explicit polynomial covectors satisfy the conformal Killing equation in a
constant diagonal metric. The coordinate rules are realized by Mathlib's
multivariate polynomial partial derivations. In dimension four, contraction
with the raised Maxwell tensor is conserved under the stated stress-divergence
equations. These equations are not inferred from symmetry or tracelessness.
-/

noncomputable section

namespace InfoGeometry.Conformal.BesselHagenGenerators

open scoped BigOperators
open InfoGeometry.Canonical.BesselHagenNoether
open InfoGeometry.Conformal.BesselHagenCurrent
open InfoGeometry.Conformal.MaxwellStressTensor

variable {A ι : Type*} [CommRing A] [Algebra ℝ A] [Fintype ι] [DecidableEq ι]

/-- Position covector obtained by lowering the coordinate vector. -/
def dilationCovector (ε x : ι → A) (i : ι) : A := ε i * x i

/-- The linear covector with an antisymmetric constant coefficient matrix. -/
def rotationCovector (K : Matrix ι ι A) (x : ι → A) (j : ι) : A :=
  ∑ k, K j k * x k

/-- The diagonal metric pairing with the constant special-conformal parameter. -/
def parameterPairing (ε b x : ι → A) : A := ∑ k, ε k * b k * x k

/-- The position quadratic form in the diagonal metric. -/
def positionSquare (ε x : ι → A) : A := ∑ k, ε k * (x k) ^ 2

/-- Lowered special-conformal field `2 g(b,x) x♭ - g(x,x) b♭`. -/
def specialConformalCovector (ε b x : ι → A) (j : ι) : A :=
  2 * parameterPairing ε b x * (ε j * x j) - positionSquare ε x * (ε j * b j)

variable (D : ι → Derivation ℝ A A) (ε x : ι → A)
variable (hε : ∀ i j, D i (ε j) = 0)
variable (hx : ∀ i j, D i (x j) = if i = j then 1 else 0)

omit [Fintype ι] in
/-- Constant translations satisfy the Killing equation with zero conformal factor. -/
theorem translation_isConformalKilling (a : ι → A)
    (ha : ∀ i j, D i (a j) = 0) :
    IsConformalKilling D (metricEntry ε) a 0 := by
  intro i j
  simp [ha]

section CoordinateRules

include hε hx

omit [Fintype ι] in
theorem deriv_dilationCovector (i j : ι) :
    D i (dilationCovector ε x j) = metricEntry ε i j := by
  simp only [dilationCovector, Derivation.leibniz, smul_eq_mul, hε, hx,
    mul_zero, add_zero, metricEntry]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

omit [Fintype ι] in
/-- The dilation has conformal factor one. -/
theorem dilation_isConformalKilling :
    IsConformalKilling D (metricEntry ε) (dilationCovector ε x) 1 := by
  intro i j
  rw [deriv_dilationCovector D ε x hε hx i j,
    deriv_dilationCovector D ε x hε hx j i, metricEntry_symm ε j i]
  ring

omit hε in
/-- Antisymmetric linear coefficients give the rotations and boosts after index lowering. -/
theorem rotation_isConformalKilling (K : Matrix ι ι A)
    (hK : ∀ i j, K i j = -K j i) (hconst : ∀ i j k, D i (K j k) = 0) :
    IsConformalKilling D (metricEntry ε) (rotationCovector K x) 0 := by
  have hd i j : D i (rotationCovector K x j) = K j i := by
    simp [rotationCovector, map_sum, Derivation.leibniz, smul_eq_mul, hconst, hx]
  intro i j
  rw [hd, hd, hK j i]
  simp

theorem deriv_parameterPairing (b : ι → A)
    (hb : ∀ i j, D i (b j) = 0) (i : ι) :
    D i (parameterPairing ε b x) = ε i * b i := by
  simp [parameterPairing, map_sum, Derivation.leibniz, smul_eq_mul, hε, hb, hx]

theorem deriv_positionSquare (i : ι) :
    D i (positionSquare ε x) = 2 * ε i * x i := by
  simp [positionSquare, map_sum, Derivation.leibniz, Derivation.leibniz_pow,
    smul_eq_mul, hε, hx, mul_assoc]
  ring

theorem deriv_specialConformalCovector (b : ι → A)
    (hb : ∀ i j, D i (b j) = 0) (i j : ι) :
    D i (specialConformalCovector ε b x j) =
      2 * (ε i * b i) * (ε j * x j) +
        2 * parameterPairing ε b x * metricEntry ε i j -
          (2 * ε i * x i) * (ε j * b j) := by
  have hl := deriv_dilationCovector D ε x hε hx i j
  change D i (ε j * x j) = metricEntry ε i j at hl
  have htwo : D i (2 : A) = 0 := (D i).map_natCast 2
  simp only [specialConformalCovector, map_sub, Derivation.leibniz,
    smul_eq_mul, htwo, hε, hb, mul_zero, add_zero,
    zero_add, deriv_parameterPairing D ε x hε hx b hb,
    deriv_positionSquare D ε x hε hx, hl]
  ring

/-- The special-conformal factor is exactly `2 g(b,x)`. -/
theorem specialConformal_isConformalKilling (b : ι → A)
    (hb : ∀ i j, D i (b j) = 0) :
    IsConformalKilling D (metricEntry ε) (specialConformalCovector ε b x)
      (2 * parameterPairing ε b x) := by
  intro i j
  rw [deriv_specialConformalCovector D ε x hε hx b hb i j,
    deriv_specialConformalCovector D ε x hε hx b hb j i,
    metricEntry_symm ε j i]
  ring

/-- Dilation-current balance, including the trace contributed by matter. -/
theorem divergence_dilationCurrent (S : Matrix ι ι A)
    (hS : ∀ i j, S i j = S j i) (hdiv : ∀ j, stressDivergence D S j = 0) :
    divergence D (stressCurrent S (dilationCovector ε x)) = contraction S (metricEntry ε) := by
  simpa using divergence_stressCurrent_eq_trace D S (metricEntry ε)
    (dilationCovector ε x) 1 hS (dilation_isConformalKilling D ε x hε hx) hdiv

/-- Special-conformal-current balance, with its exact trace obstruction. -/
theorem divergence_specialConformalCurrent (S : Matrix ι ι A) (b : ι → A)
    (hb : ∀ i j, D i (b j) = 0)
    (hS : ∀ i j, S i j = S j i) (hdiv : ∀ j, stressDivergence D S j = 0) :
    divergence D (stressCurrent S (specialConformalCovector ε b x)) =
      (2 * parameterPairing ε b x) * contraction S (metricEntry ε) := by
  exact divergence_stressCurrent_eq_trace D S (metricEntry ε)
    (specialConformalCovector ε b x) (2 * parameterPairing ε b x) hS
    (specialConformal_isConformalKilling D ε x hε hx b hb) hdiv

end CoordinateRules

/-- The actual four-dimensional Maxwell tensor instantiates the conformal-current theorem. -/
theorem maxwell_conformalCurrent_conserved
    (D : Fin 4 → Derivation ℝ A A) (ε : Fin 4 → A)
    (hε : ∀ i, ε i * ε i = 1) (F : Matrix (Fin 4) (Fin 4) A)
    (ξ : Fin 4 → A) (σ : A)
    (hξ : IsConformalKilling D (metricEntry ε) ξ σ)
    (hdiv : ∀ j, stressDivergence D (raisedTensor ε F) j = 0) :
    divergence D (stressCurrent (raisedTensor ε F) ξ) = 0 := by
  apply stressCurrent_conserved D (raisedTensor ε F) (metricEntry ε) ξ σ
    (raisedTensor_symm ε F) hξ hdiv
  simpa only [contraction, mul_comm] using metric_contraction_raisedTensor_fin4 ε hε F

omit [Fintype ι] in
/-- A concrete native differential algebra realizes the coordinate hypotheses. -/
theorem polynomial_coordinates (i j : ι) :
    MvPolynomial.pderiv i (MvPolynomial.X j : MvPolynomial ι ℝ) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · simp only [MvPolynomial.pderiv_X_of_ne (Ne.symm hij), hij, ite_false]

/-- The special-conformal generator is realized by actual polynomial derivations. -/
theorem polynomial_specialConformal_isConformalKilling (ε b : ι → ℝ) :
    IsConformalKilling (fun i => MvPolynomial.pderiv i)
      (metricEntry (fun i => MvPolynomial.C (ε i)))
      (specialConformalCovector (fun i => MvPolynomial.C (ε i))
        (fun i => MvPolynomial.C (b i)) MvPolynomial.X)
      (2 * parameterPairing (fun i => MvPolynomial.C (ε i))
        (fun i => MvPolynomial.C (b i)) MvPolynomial.X) := by
  exact specialConformal_isConformalKilling
    (fun i => MvPolynomial.pderiv i) (fun i => MvPolynomial.C (ε i)) MvPolynomial.X
    (fun _ _ => MvPolynomial.pderiv_C) polynomial_coordinates
    (fun i => MvPolynomial.C (b i)) (fun _ _ => MvPolynomial.pderiv_C)

/-- Constant real fields give a genuinely conserved polynomial stress tensor. -/
theorem polynomial_constant_stressDivergence_zero (ε : ι → ℝ)
    (F : Matrix ι ι ℝ) (j : ι) :
    stressDivergence (fun i => MvPolynomial.pderiv i)
      (raisedTensor (fun i => MvPolynomial.C (ε i))
        (fun i j => MvPolynomial.C (F i j))) j = 0 := by
  simp [stressDivergence, raisedTensor, tensor, fieldSquare, metricEntry,
    map_sum, Derivation.leibniz, smul_eq_mul, apply_ite]

/-- Concrete polynomial Maxwell special-conformal currents, with stress conservation discharged.
This is a constant-field example; it does not infer conservation for a variable field. -/
theorem polynomial_constantMaxwell_specialCurrent_conserved (ε b : Fin 4 → ℝ)
    (hε : ∀ i, ε i * ε i = 1) (F : Matrix (Fin 4) (Fin 4) ℝ) :
    divergence (fun i => MvPolynomial.pderiv i)
      (stressCurrent
        (raisedTensor (fun i => MvPolynomial.C (ε i))
          (fun i j => MvPolynomial.C (F i j)))
        (specialConformalCovector (fun i => MvPolynomial.C (ε i))
          (fun i => MvPolynomial.C (b i)) MvPolynomial.X)) = 0 := by
  have hεpoly : ∀ i : Fin 4,
      (MvPolynomial.C (ε i) : MvPolynomial (Fin 4) ℝ) * MvPolynomial.C (ε i) = 1 := by
    intro i
    rw [← map_mul, hε i, map_one]
  exact maxwell_conformalCurrent_conserved
    (fun i => MvPolynomial.pderiv i) (fun i => MvPolynomial.C (ε i)) hεpoly
    (fun i j => MvPolynomial.C (F i j)) _ _
    (polynomial_specialConformal_isConformalKilling ε b)
    (polynomial_constant_stressDivergence_zero ε F)

end InfoGeometry.Conformal.BesselHagenGenerators
