import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Noncommutative Rényi operator kernels

This file owns the operator expressions underlying the Petz and sandwiched
Rényi constructions.  It deliberately stops before taking a logarithm or
dividing by `α - 1`: those are downstream scalar readouts and require
positivity/nonvanishing hypotheses on the chosen functional.

No simultaneous diagonalization is used.  Real powers are Mathlib continuous
functional calculus powers in the ambient noncommutative C-star algebra.
-/

namespace InfoGeometry.OperatorAlgebra.NoncommutativeRenyi

open scoped ComplexOrder

variable {A : Type*}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A positive functional is tracial when it is cyclic on every product. -/
def IsTracial (τ : A →ₚ[ℂ] ℂ) : Prop :=
  ∀ a b : A, τ (a * b) = τ (b * a)

/--
The Petz Rényi operator kernel

`ρ ^ α * σ ^ (1 - α)`.

The order of multiplication is part of the definition and is not erased by a
commutativity or diagonalizability assumption.
-/
noncomputable def petzKernel (α : ℝ) (ρ σ : A) : A :=
  ρ ^ α * σ ^ (1 - α)

/--
The exponent used to conjugate `ρ` in the sandwiched Rényi kernel.

The order `α = 0` is excluded by the mathematical application, but the
operator expression is kept total at the definition level.  The appropriate
nonzero/order hypothesis belongs on the theorem that consumes it.
-/
noncomputable def sandwichExponent (α : ℝ) : ℝ :=
  (1 - α) / (2 * α)

/--
The positive-conjugation expression occurring before the outer Rényi power:

`σ ^ ((1 - α) / (2 * α)) * ρ * σ ^ ((1 - α) / (2 * α))`.
-/
noncomputable def sandwichedCore (α : ℝ) (ρ σ : A) : A :=
  star (σ ^ sandwichExponent α) * ρ * σ ^ sandwichExponent α

/--
The sandwiched Rényi operator kernel

`(σ ^ ((1 - α) / (2 * α)) * ρ *
    σ ^ ((1 - α) / (2 * α))) ^ α`.
-/
noncomputable def sandwichedKernel (α : ℝ) (ρ σ : A) : A :=
  sandwichedCore α ρ σ ^ α

/--
The operator-valued state surprisal `-log ρ`, formed by Mathlib continuous
functional calculus in the ambient noncommutative C-star algebra.

This is not a scalar entropy and no trace or simultaneous diagonalization is
taken here.
-/
noncomputable def stateSurprisal (ρ : A) : A :=
  -cfc Real.log ρ

/--
The relative log-density operator `log ρ - log σ`.

It is the noncommutative logarithmic likelihood-ratio kernel before weighting
by the source state or applying a positive functional.
-/
noncomputable def relativeLogDensity (ρ σ : A) : A :=
  cfc Real.log ρ - cfc Real.log σ

/--
The Umegaki relative-entropy operator kernel

`ρ * (log ρ - log σ)`.

The multiplication order is retained.  A scalar relative entropy is only a
downstream readout of this operator through an explicitly supplied positive
functional.
-/
noncomputable def umegakiKernel (ρ σ : A) : A :=
  ρ * relativeLogDensity ρ σ

/-- Downstream Petz moment supplied by a genuine Mathlib positive functional. -/
noncomputable def petzMoment
    (τ : A →ₚ[ℂ] ℂ) (α : ℝ) (ρ σ : A) : ℂ :=
  τ (petzKernel α ρ σ)

/--
Downstream sandwiched moment supplied by a genuine Mathlib positive
functional.
-/
noncomputable def sandwichedMoment
    (τ : A →ₚ[ℂ] ℂ) (α : ℝ) (ρ σ : A) : ℂ :=
  τ (sandwichedKernel α ρ σ)

/--
The Umegaki relative-entropy readout of the operator kernel through a genuine
Mathlib positive functional.
-/
noncomputable def umegakiRelativeEntropy
    (τ : A →ₚ[ℂ] ℂ) (ρ σ : A) : ℂ :=
  τ (umegakiKernel ρ σ)

@[simp]
theorem stateSurprisal_apply (ρ : A) :
    stateSurprisal ρ = -cfc Real.log ρ :=
  rfl

@[simp]
theorem relativeLogDensity_apply (ρ σ : A) :
    relativeLogDensity ρ σ = cfc Real.log ρ - cfc Real.log σ :=
  rfl

@[simp]
theorem relativeLogDensity_self (ρ : A) :
    relativeLogDensity ρ ρ = 0 := by
  simp [relativeLogDensity]

@[simp]
theorem umegakiKernel_apply (ρ σ : A) :
    umegakiKernel ρ σ = ρ * (cfc Real.log ρ - cfc Real.log σ) :=
  rfl

@[simp]
theorem umegakiKernel_self (ρ : A) :
    umegakiKernel ρ ρ = 0 := by
  simp [umegakiKernel]

@[simp]
theorem umegakiRelativeEntropy_apply
    (τ : A →ₚ[ℂ] ℂ) (ρ σ : A) :
    umegakiRelativeEntropy τ ρ σ =
      τ (ρ * (cfc Real.log ρ - cfc Real.log σ)) :=
  rfl

@[simp]
theorem umegakiRelativeEntropy_self
    (τ : A →ₚ[ℂ] ℂ) (ρ : A) :
    umegakiRelativeEntropy τ ρ ρ = 0 := by
  simp [umegakiRelativeEntropy]

@[simp]
theorem petzMoment_apply
    (τ : A →ₚ[ℂ] ℂ) (α : ℝ) (ρ σ : A) :
    petzMoment τ α ρ σ = τ (ρ ^ α * σ ^ (1 - α)) :=
  rfl

@[simp]
theorem sandwichedMoment_apply
    (τ : A →ₚ[ℂ] ℂ) (α : ℝ) (ρ σ : A) :
    sandwichedMoment τ α ρ σ =
      τ ((star (σ ^ ((1 - α) / (2 * α))) * ρ *
        σ ^ ((1 - α) / (2 * α))) ^ α) :=
  rfl

/--
The sandwiched core is positive whenever the state operator `ρ` is positive.

This is the native star-ordered-ring conjugation theorem; no commutation or
diagonalization hypothesis is used.
-/
theorem sandwichedCore_nonneg
    (α : ℝ) {ρ σ : A} (hρ : 0 ≤ ρ) :
    0 ≤ sandwichedCore α ρ σ := by
  exact star_left_conjugate_nonneg hρ (σ ^ sandwichExponent α)

/-- The outer CFC real power keeps the sandwiched Rényi kernel positive. -/
theorem sandwichedKernel_nonneg
    (α : ℝ) (ρ σ : A) :
    0 ≤ sandwichedKernel α ρ σ :=
  CFC.rpow_nonneg

/-- Traciality is symmetric under swapping the two factors. -/
theorem IsTracial.swap
    {τ : A →ₚ[ℂ] ℂ} (hτ : IsTracial τ) (a b : A) :
    τ (b * a) = τ (a * b) :=
  (hτ a b).symm

end InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
