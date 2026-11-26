/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Canonical.DrazinInfiniteCore

/-!
# InfoGeometry/Canonical/DunfordTaylor.lean

Dunford-Taylor functional-calculus roadmap for bounded operators on complex
Banach spaces.

This file records a stable API surface for:

* the resolvent set of a bounded operator;
* the total Mathlib resolvent;
* Dunford-Taylor contour integrals;
* Riesz projections;
* the bounded-operator Koliha-Drazin contour expression.

Important design point:

The raw expression

  `P = (2πi)⁻¹ ∮ (zI - A)⁻¹ dz`

is not idempotent for an arbitrary path `γ : ℝ → ℂ`. Idempotence and
range-invariance require spectral-separation and contour-admissibility
hypotheses. This file therefore proves the genuine algebraic resolvent
identities and packages the Riesz projection laws behind an admissibility
certificate, rather than asserting false theorem-shaped placeholders.
-/

namespace InfoGeometry.Canonical

open MeasureTheory
open Topology
open Complex
noncomputable section

/-- Bounded complex-linear endomorphisms of `E`. -/
abbrev BoundedEnd
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :=
  E →L[ℂ] E

section AlgebraicResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local notation "EndH" => BoundedEnd E

/--
The resolvent set of a bounded operator.

This is the Mathlib resolvent set specialized to the Banach algebra
`E →L[ℂ] E`.
-/
abbrev resolventSet (A : EndH) : Set ℂ :=
  _root_.resolventSet ℂ A

/--
The total Mathlib resolvent specialized to bounded complex-linear operators.

On the resolvent set this is the inverse of `z • I - A`; off the resolvent set
Mathlib's total inverse convention returns the ring inverse value.
-/
abbrev resolvent (A : EndH) (z : ℂ) : EndH :=
  _root_.resolvent A z

omit [CompleteSpace E] in
/-- The local alias `resolventSet` is the complement of the spectrum. -/
theorem resolventSet_eq_compl_spectrum (A : EndH) :
    resolventSet A = (spectrum ℂ A)ᶜ := by
  ext z
  simp [resolventSet, spectrum]

omit [CompleteSpace E] in
/-- Membership in the resolvent set means that `z • I - A` is a unit. -/
@[simp]
theorem mem_resolventSet_iff (A : EndH) (z : ℂ) :
    z ∈ resolventSet A ↔ IsUnit (z • (1 : EndH) - A) := by
  simp [resolventSet, _root_.resolventSet, Algebra.algebraMap_eq_smul_one]

/-- The resolvent set is open. -/
theorem isOpen_resolventSet (A : EndH) :
    IsOpen (resolventSet A) := by
  rw [resolventSet_eq_compl_spectrum]
  exact (spectrum.isClosed A).isOpen_compl

omit [CompleteSpace E] in
/-- Left resolvent identity: `(zI - A) R(z,A) = I`. -/
theorem resolvent_id_left (A : EndH) {z : ℂ}
    (hz : z ∈ resolventSet A) :
    (z • (1 : EndH) - A) * resolvent A z = 1 := by
  change IsUnit (algebraMap ℂ EndH z - A) at hz
  simp [resolvent, Algebra.algebraMap_eq_smul_one,
    spectrum.resolvent_eq (a := A) (r := z) hz]

omit [CompleteSpace E] in
/-- Right resolvent identity: `R(z,A) (zI - A) = I`. -/
theorem resolvent_id_right (A : EndH) {z : ℂ}
    (hz : z ∈ resolventSet A) :
    resolvent A z * (z • (1 : EndH) - A) = 1 := by
  change IsUnit (algebraMap ℂ EndH z - A) at hz
  simp [resolvent, Algebra.algebraMap_eq_smul_one,
    spectrum.resolvent_eq (a := A) (r := z) hz]

end AlgebraicResolvent

section DunfordTaylorIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local notation "EndH" => BoundedEnd E

/--
Dunford-Taylor integral of a continuous function `f` on a contour `γ`
with values in the Banach algebra of bounded operators.

This is intentionally only a syntactic API placeholder. The future production
version should use an admissible contour type carrying differentiability,
piecewise smoothness, winding-number, and resolvent-avoidance hypotheses.
-/
def dunfordTaylorIntegral
    (γ : ℝ → ℂ) (f : ℂ → EndH) (a b : ℝ) : EndH :=
  ∫ t, deriv γ t • f (γ t) ∂(volume.restrict (Set.Icc a b))

omit [CompleteSpace E] in
/-- The Dunford-Taylor integral of the zero function is zero. -/
@[simp]
theorem dunfordTaylorIntegral_zero_function
    (γ : ℝ → ℂ) (a b : ℝ) :
    dunfordTaylorIntegral γ (fun _ => (0 : EndH)) a b = 0 := by
  simp [dunfordTaylorIntegral]

omit [CompleteSpace E] in
/-- The Dunford-Taylor integral over a constant contour is zero. -/
@[simp]
theorem dunfordTaylorIntegral_const_contour
    (z₀ : ℂ) (f : ℂ → EndH) (a b : ℝ) :
    dunfordTaylorIntegral (fun _ : ℝ => z₀) f a b = 0 := by
  simp [dunfordTaylorIntegral]

/--
The Riesz projection associated to a contour expression:

`P = (2πi)⁻¹ ∮_Γ (zI - A)⁻¹ dz`.
-/
def rieszProjection (A : EndH) (γ : ℝ → ℂ) (a b : ℝ) : EndH :=
  (1 / (2 * (Real.pi : ℂ) * I)) •
    dunfordTaylorIntegral γ (resolvent A) a b

omit [CompleteSpace E] in
/-- Resolvent bounds on a contour parameter interval give a quantitative
stability estimate for the actual Bochner path integral. The hypotheses make
no claim that the path is admissible or that its integral is idempotent. -/
theorem norm_dunfordTaylorIntegral_resolvent_sub_le
    (A B : EndH) (γ : ℝ → ℂ) (a b L M : ℝ)
    [IsFiniteMeasure (volume.restrict (Set.Icc a b))]
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hresA : ∀ t ∈ Set.Icc a b, γ t ∈ resolventSet A)
    (hresB : ∀ t ∈ Set.Icc a b, γ t ∈ resolventSet B)
    (hboundA : ∀ t ∈ Set.Icc a b, ‖resolvent A (γ t)‖ ≤ M)
    (hboundB : ∀ t ∈ Set.Icc a b, ‖resolvent B (γ t)‖ ≤ M)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖deriv γ t‖ ≤ L)
    (hintA : Integrable (fun t => deriv γ t • resolvent A (γ t))
      (volume.restrict (Set.Icc a b)))
    (hintB : Integrable (fun t => deriv γ t • resolvent B (γ t))
      (volume.restrict (Set.Icc a b))) :
    ‖dunfordTaylorIntegral γ (resolvent A) a b -
      dunfordTaylorIntegral γ (resolvent B) a b‖ ≤
      (L * M ^ 2 * ‖A - B‖) * (volume.restrict (Set.Icc a b)).real Set.univ := by
  let μ := volume.restrict (Set.Icc a b)
  let fA : ℝ → EndH := fun t => deriv γ t • resolvent A (γ t)
  let fB : ℝ → EndH := fun t => deriv γ t • resolvent B (γ t)
  have hsub : Integrable (fun t => fA t - fB t) μ := hintA.sub hintB
  have hnorm : ∀ᵐ t ∂μ, ‖fA t - fB t‖ ≤ L * M ^ 2 * ‖A - B‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hres := spectrum.resolvent_sub_resolvent (hresA t ht) (hresB t ht)
    have hdiff : ‖resolvent A (γ t) - resolvent B (γ t)‖ ≤
        M ^ 2 * ‖A - B‖ := by
      rw [hres]
      calc
        ‖resolvent A (γ t) * (A - B) * resolvent B (γ t)‖ ≤
            ‖resolvent A (γ t)‖ * ‖A - B‖ * ‖resolvent B (γ t)‖ := by
              calc
                _ ≤ ‖resolvent A (γ t) * (A - B)‖ *
                    ‖resolvent B (γ t)‖ := norm_mul_le _ _
                _ ≤ (‖resolvent A (γ t)‖ * ‖A - B‖) *
                    ‖resolvent B (γ t)‖ := by
                      exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ M * ‖A - B‖ * M := by
              gcongr <;> first | exact hboundA t ht | exact hboundB t ht
        _ = M ^ 2 * ‖A - B‖ := by ring
    calc
      ‖fA t - fB t‖ = ‖deriv γ t •
          (resolvent A (γ t) - resolvent B (γ t))‖ := by
            simp [fA, fB, smul_sub]
      _ = ‖deriv γ t‖ *
          ‖resolvent A (γ t) - resolvent B (γ t)‖ := norm_smul _ _
      _ ≤ L * (M ^ 2 * ‖A - B‖) := by
            exact mul_le_mul (hderiv t ht) hdiff (norm_nonneg _) hL
      _ = L * M ^ 2 * ‖A - B‖ := by ring
  rw [dunfordTaylorIntegral, dunfordTaylorIntegral, ← integral_sub hintA hintB]
  simpa [μ, fA, fB, mul_assoc] using
    (norm_integral_le_of_norm_le_const hnorm)

omit [CompleteSpace E] in
/-- The normalized Riesz contour expressions inherit the same Lipschitz
stability estimate, multiplied by the norm of the fixed contour normalizer.
This estimate alone does not establish the Riesz projection laws. -/
theorem norm_rieszProjection_sub_le
    (A B : EndH) (γ : ℝ → ℂ) (a b L M : ℝ)
    [IsFiniteMeasure (volume.restrict (Set.Icc a b))]
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hresA : ∀ t ∈ Set.Icc a b, γ t ∈ resolventSet A)
    (hresB : ∀ t ∈ Set.Icc a b, γ t ∈ resolventSet B)
    (hboundA : ∀ t ∈ Set.Icc a b, ‖resolvent A (γ t)‖ ≤ M)
    (hboundB : ∀ t ∈ Set.Icc a b, ‖resolvent B (γ t)‖ ≤ M)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖deriv γ t‖ ≤ L)
    (hintA : Integrable (fun t => deriv γ t • resolvent A (γ t))
      (volume.restrict (Set.Icc a b)))
    (hintB : Integrable (fun t => deriv γ t • resolvent B (γ t))
      (volume.restrict (Set.Icc a b))) :
    ‖rieszProjection A γ a b - rieszProjection B γ a b‖ ≤
      ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ *
        ((L * M ^ 2 * ‖A - B‖) *
          (volume.restrict (Set.Icc a b)).real Set.univ) := by
  rw [rieszProjection, rieszProjection, ← smul_sub]
  calc
    ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ) •
        (dunfordTaylorIntegral γ (resolvent A) a b -
          dunfordTaylorIntegral γ (resolvent B) a b)‖ ≤
        ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ *
          ‖dunfordTaylorIntegral γ (resolvent A) a b -
            dunfordTaylorIntegral γ (resolvent B) a b‖ := le_of_eq (norm_smul _ _)
    _ ≤ ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ *
        ((L * M ^ 2 * ‖A - B‖) *
          (volume.restrict (Set.Icc a b)).real Set.univ) := by
      gcongr
      exact norm_dunfordTaylorIntegral_resolvent_sub_le A B γ a b L M hL hM
        hresA hresB hboundA hboundB hderiv hintA hintB

omit [CompleteSpace E] in
/-- A small operator perturbation transports the resolvent bound along the
contour and therefore supplies the hypotheses for the Riesz-expression
stability estimate. Integrability of both parameterized resolvents remains
explicit; this theorem does not assert admissibility or idempotence. -/
theorem norm_rieszProjection_sub_le_of_uniform_perturbation
    (A B : EndH) (γ : ℝ → ℂ) (a b L M : ℝ)
    [IsFiniteMeasure (volume.restrict (Set.Icc a b))]
    [HasSummableGeomSeries EndH] [Nontrivial EndH]
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hresA : ∀ t ∈ Set.Icc a b, γ t ∈ resolventSet A)
    (hboundA : ∀ t ∈ Set.Icc a b, ‖resolvent A (γ t)‖ ≤ M)
    (hperturb : ‖A - B‖ * M < 1)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖deriv γ t‖ ≤ L)
    (hintA : Integrable (fun t => deriv γ t • resolvent A (γ t))
      (volume.restrict (Set.Icc a b)))
    (hintB : Integrable (fun t => deriv γ t • resolvent B (γ t))
      (volume.restrict (Set.Icc a b))) :
    ‖rieszProjection A γ a b - rieszProjection B γ a b‖ ≤
      ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ *
        (((L * (M / (1 - ‖A - B‖ * M)) ^ 2 * ‖A - B‖) *
          (volume.restrict (Set.Icc a b)).real Set.univ)) := by
  let M' := M / (1 - ‖A - B‖ * M)
  have hden : 0 < 1 - ‖A - B‖ * M := by linarith
  have hM' : 0 ≤ M' := by
    dsimp [M']
    exact div_nonneg hM hden.le
  have hMle : M ≤ M' := by
    dsimp [M']
    rw [le_div_iff₀ hden]
    have hδ : 0 ≤ ‖A - B‖ := norm_nonneg _
    have hprod : 0 ≤ ‖A - B‖ * M := mul_nonneg hδ hM
    have hsq : 0 ≤ M * (‖A - B‖ * M) := mul_nonneg hM hprod
    nlinarith
  have hresA' : ∀ z ∈ γ '' Set.Icc a b, z ∈ _root_.resolventSet ℂ A := by
    rintro z ⟨t, ht, rfl⟩
    exact hresA t ht
  have hboundA' : ∀ z ∈ γ '' Set.Icc a b, ‖_root_.resolvent A z‖ ≤ M := by
    rintro z ⟨t, ht, rfl⟩
    exact hboundA t ht
  have hperturbed :=
    InfoGeometry.Canonical.DrazinInfiniteCore.resolvent_norm_bound_of_uniform_perturbation
      A B (γ '' Set.Icc a b) M hresA' hboundA' hperturb
  have hresB : ∀ t ∈ Set.Icc a b, γ t ∈ resolventSet B := by
    intro t ht
    exact (hperturbed (γ t) ⟨t, ht, rfl⟩).1
  have hboundB : ∀ t ∈ Set.Icc a b, ‖resolvent B (γ t)‖ ≤ M' := by
    intro t ht
    simpa [M'] using (hperturbed (γ t) ⟨t, ht, rfl⟩).2
  have hboundA'contour : ∀ t ∈ Set.Icc a b, ‖resolvent A (γ t)‖ ≤ M' := by
    intro t ht
    exact (hboundA t ht).trans hMle
  exact norm_rieszProjection_sub_le A B γ a b L M' hL hM'
    hresA hresB hboundA'contour hboundB hderiv hintA hintB

omit [CompleteSpace E] in
/-- The Riesz-projection expression over a constant contour is zero. -/
@[simp]
theorem rieszProjection_const_contour
    (A : EndH) (z₀ : ℂ) (a b : ℝ) :
    rieszProjection A (fun _ : ℝ => z₀) a b = 0 := by
  simp [rieszProjection, dunfordTaylorIntegral]

/--
The bounded-operator Koliha-Drazin contour expression around the core
nonzero spectral component:

`Aᴰ = (2πi)⁻¹ ∮Γ z⁻¹ (zI - A)⁻¹ dz`.

For unbounded closed operators this should later be replaced by the
Riemann-sphere/holomorphic-functional-calculus formulation.
-/
def kolihaDrazinInverse (A : EndH) (γ : ℝ → ℂ) (a b : ℝ) : EndH :=
  (1 / (2 * (Real.pi : ℂ) * I)) •
    dunfordTaylorIntegral γ (fun z => (z⁻¹ : ℂ) • resolvent A z) a b

omit [CompleteSpace E] in
/-- The Koliha-Drazin contour expression over a constant contour is zero. -/
@[simp]
theorem kolihaDrazinInverse_const_contour
    (A : EndH) (z₀ : ℂ) (a b : ℝ) :
    kolihaDrazinInverse A (fun _ : ℝ => z₀) a b = 0 := by
  simp [kolihaDrazinInverse, dunfordTaylorIntegral]

namespace RieszProjection

/-- Statement of the left resolvent identity. -/
def resolventIdLeftStatement (A : EndH) (z : ℂ) : Prop :=
  z ∈ resolventSet A →
    (z • (1 : EndH) - A) * resolvent A z = 1

/-- Statement of the right resolvent identity. -/
def resolventIdRightStatement (A : EndH) (z : ℂ) : Prop :=
  z ∈ resolventSet A →
    resolvent A z * (z • (1 : EndH) - A) = 1

omit [CompleteSpace E] in
/-- The left resolvent identity, proved from Mathlib's resolvent. -/
theorem resolventIdLeftStatement_proof (A : EndH) (z : ℂ) :
    resolventIdLeftStatement A z := by
  intro hz
  exact resolvent_id_left A hz

omit [CompleteSpace E] in
/-- The right resolvent identity, proved from Mathlib's resolvent. -/
theorem resolventIdRightStatement_proof (A : EndH) (z : ℂ) :
    resolventIdRightStatement A z := by
  intro hz
  exact resolvent_id_right A hz

/-- Statement that the Riesz contour expression is idempotent. -/
def idempotentStatement (A : EndH) (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  let P := rieszProjection A γ a b
  P * P = P

/-- Statement that the Riesz contour expression commutes with `A`. -/
def rangeInvariantStatement (A : EndH) (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  let P := rieszProjection A γ a b
  A * P = P * A

omit [CompleteSpace E] in
/--
A degenerate proof: the constant-contour Riesz expression is zero, hence
idempotent.
-/
theorem idempotentStatement_const_contour
    (A : EndH) (z₀ : ℂ) (a b : ℝ) :
    idempotentStatement A (fun _ : ℝ => z₀) a b := by
  simp [idempotentStatement]

omit [CompleteSpace E] in
/--
A degenerate proof: the constant-contour Riesz expression is zero, hence it
commutes with `A`.
-/
theorem rangeInvariantStatement_const_contour
    (A : EndH) (z₀ : ℂ) (a b : ℝ) :
    rangeInvariantStatement A (fun _ : ℝ => z₀) a b := by
  simp [rangeInvariantStatement]

/--
Future proof payload for an admissible Riesz contour.

The general facts `P² = P` and `AP = PA` require genuine contour and
functional-calculus hypotheses. Until those are formalized, downstream code
should depend on this proof-carrying structure rather than on unconditional
roadmap theorems.
-/
def AdmissibleRieszProjectionLaws
    (A : EndH) (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  idempotentStatement A γ a b ∧
  rangeInvariantStatement A γ a b

omit [CompleteSpace E] in
/-- Extract idempotence from admissible-contour laws. -/
theorem idempotent_of_admissible
    {A : EndH} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AdmissibleRieszProjectionLaws A γ a b) :
    idempotentStatement A γ a b :=
  hγ.1

omit [CompleteSpace E] in
/-- Extract range invariance from admissible-contour laws. -/
theorem rangeInvariant_of_admissible
    {A : EndH} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AdmissibleRieszProjectionLaws A γ a b) :
    rangeInvariantStatement A γ a b :=
  hγ.2

end RieszProjection

end DunfordTaylorIntegral

end

end InfoGeometry.Canonical
