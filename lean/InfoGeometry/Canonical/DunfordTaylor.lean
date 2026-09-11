import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Algebra.Spectrum

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
