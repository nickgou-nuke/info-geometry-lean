import InfoGeometry.KL.Measure
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Jaynesian MaxEnt (Measure-Theoretic Core)

Core scaffold for Jaynes-style maximum entropy:

- feasible variables: probability measures absolutely continuous w.r.t. a prior
- constraints: linear moment equalities
- objective: minimize `KL(μ || μ₀)` over feasible measures

This file is intentionally structural and theorem-light. It provides a clean
interface for later variational/Fenchel development.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace InfoGeometry.MaxEnt

variable {Ω : Type _} [MeasurableSpace Ω]

/-- Probability measures absolutely continuous with respect to a prior `μ₀`. -/
structure ACProbMeasure (μ₀ : Measure Ω) where
  μ : Measure Ω
  prob : μ Set.univ = 1
  ac : μ ≪ μ₀

namespace ACProbMeasure

variable {μ₀ : Measure Ω}

instance (μ₀ : Measure Ω) : CoeTC (ACProbMeasure μ₀) (Measure Ω) := ⟨fun P => P.μ⟩

/-- `ACProbMeasure` carries the canonical `IsProbabilityMeasure` instance. -/
instance (P : ACProbMeasure μ₀) : IsProbabilityMeasure P.μ :=
  ⟨by simpa using P.prob⟩

/-- Equality of underlying measures implies equality after coercion. -/
lemma coe_eq_of_measure_eq {P Q : ACProbMeasure μ₀} (h : P.μ = Q.μ) :
    (P : Measure Ω) = (Q : Measure Ω) := by
  simpa using h

end ACProbMeasure

/-- A linear moment constraint `∫ f dμ = c`. -/
structure LinearConstraint (Ω : Type _) [MeasurableSpace Ω] where
  f : Ω → ℝ
  measurable_f : Measurable f
  c : ℝ

namespace LinearConstraint

variable {Ω : Type _} [MeasurableSpace Ω]

/-- Satisfaction predicate for a single moment constraint. -/
def Satisfies (μ : Measure Ω) (C : LinearConstraint Ω) : Prop :=
  ∫ x, C.f x ∂μ = C.c

/-- Integrability predicate for a single moment constraint. -/
def IntegrableUnder (μ : Measure Ω) (C : LinearConstraint Ω) : Prop :=
  Integrable C.f μ

/-- Strong satisfaction: integrability plus moment equality. -/
def SatisfiesIntegrable (μ : Measure Ω) (C : LinearConstraint Ω) : Prop :=
  IntegrableUnder (μ := μ) C ∧ Satisfies (μ := μ) C

/-- Projection of integrability from `SatisfiesIntegrable`. -/
lemma SatisfiesIntegrable.integrable
    {μ : Measure Ω} {C : LinearConstraint Ω}
    (hC : SatisfiesIntegrable (μ := μ) C) :
    IntegrableUnder (μ := μ) C :=
  hC.1

/-- Projection of moment equality from `SatisfiesIntegrable`. -/
lemma SatisfiesIntegrable.satisfies
    {μ : Measure Ω} {C : LinearConstraint Ω}
    (hC : SatisfiesIntegrable (μ := μ) C) :
    Satisfies (μ := μ) C :=
  hC.2

end LinearConstraint

section Feasible

variable (μ₀ : Measure Ω)

/-- Feasible set: AC probabilities satisfying every constraint in a set. -/
def Feasible (constraints : Set (LinearConstraint Ω)) : Set (ACProbMeasure μ₀) :=
  { P | ∀ C ∈ constraints, LinearConstraint.Satisfies (μ := P.μ) C }

/-- Integrability-aware feasible set: all constraints are integrable and satisfied. -/
def FeasibleIntegrable (constraints : Set (LinearConstraint Ω)) : Set (ACProbMeasure μ₀) :=
  { P | ∀ C ∈ constraints, LinearConstraint.SatisfiesIntegrable (μ := P.μ) C }

/-- Set-level integrability of constraints under a given measure. -/
def ConstraintsIntegrableOn
    (μ : Measure Ω)
    (constraints : Set (LinearConstraint Ω)) : Prop :=
  ∀ C ∈ constraints, LinearConstraint.IntegrableUnder (μ := μ) C

/-- Integrability-aware feasibility implies plain feasibility. -/
lemma FeasibleIntegrable_subset_Feasible
    (constraints : Set (LinearConstraint Ω)) :
    FeasibleIntegrable (μ₀ := μ₀) constraints ⊆ Feasible (μ₀ := μ₀) constraints := by
  intro P hP C hC
  exact (hP C hC).satisfies

/-- Members of `FeasibleIntegrable` satisfy integrability for all constraints. -/
lemma ConstraintsIntegrableOn_of_memFeasibleIntegrable
    (constraints : Set (LinearConstraint Ω))
    {P : ACProbMeasure μ₀}
    (hP : P ∈ FeasibleIntegrable (μ₀ := μ₀) constraints) :
    ConstraintsIntegrableOn (μ := P.μ) constraints := by
  intro C hC
  exact (hP C hC).integrable

/-- KL objective over the feasible set. -/
noncomputable def Objective (P : ACProbMeasure μ₀) : ℝ≥0∞ :=
  InfoGeometry.KL.kl_div P.μ μ₀

/-- MaxEnt optimality as constrained minimization of KL divergence. -/
def IsMaxEntSolution
    (constraints : Set (LinearConstraint Ω))
    (P : ACProbMeasure μ₀) : Prop :=
  P ∈ Feasible (μ₀ := μ₀) constraints ∧
    ∀ Q, Q ∈ Feasible (μ₀ := μ₀) constraints →
      Objective (μ₀ := μ₀) P ≤ Objective (μ₀ := μ₀) Q

/-- MaxEnt optimality on the integrability-aware feasible set. -/
def IsMaxEntSolutionIntegrable
    (constraints : Set (LinearConstraint Ω))
    (P : ACProbMeasure μ₀) : Prop :=
  P ∈ FeasibleIntegrable (μ₀ := μ₀) constraints ∧
    ∀ Q, Q ∈ FeasibleIntegrable (μ₀ := μ₀) constraints →
      Objective (μ₀ := μ₀) P ≤ Objective (μ₀ := μ₀) Q

/-- Promote plain optimality to integrability-aware optimality when feasible-integrable. -/
lemma IsMaxEntSolution.toIntegrable
    (constraints : Set (LinearConstraint Ω))
    {P : ACProbMeasure μ₀}
    (hP : IsMaxEntSolution (μ₀ := μ₀) constraints P)
    (hPint : P ∈ FeasibleIntegrable (μ₀ := μ₀) constraints) :
    IsMaxEntSolutionIntegrable (μ₀ := μ₀) constraints P := by
  refine ⟨hPint, ?_⟩
  intro Q hQ
  exact hP.2 Q ((FeasibleIntegrable_subset_Feasible (μ₀ := μ₀) constraints) hQ)

end Feasible

/-!
## Exponential-Family Shape (Target Interface)

`HasExponentialRNForm` records the expected RN-derivative form with respect to
the prior `μ₀`. This is a target predicate for future existence/uniqueness
theorems.
-/

/-- Exponential-form Radon-Nikodym density relative to `μ₀`. -/
def HasExponentialRNForm
    (μ₀ : Measure Ω)
    (constraints : Finset (LinearConstraint Ω))
    (Λ : constraints → ℝ)
    (P : ACProbMeasure μ₀) : Prop :=
  ∃ Z : ℝ,
    0 < Z ∧
      (∀ᵐ x ∂μ₀,
        (P.μ.rnDeriv μ₀ x).toReal =
          Real.exp (∑ i : constraints, Λ i * (i.1.f x)) / Z)

/-- Sigma-finite specialization of `HasExponentialRNForm`. -/
def HasExponentialRNFormSigmaFinite
    (μ₀ : Measure Ω) [SigmaFinite μ₀]
    (constraints : Finset (LinearConstraint Ω))
    (Λ : constraints → ℝ)
    (P : ACProbMeasure μ₀) : Prop :=
  by
    let _ := (inferInstance : SigmaFinite μ₀)
    exact HasExponentialRNForm μ₀ constraints Λ P

/-!
## Dual/Fenchel Finite-Support API

This section exposes the proved finite-support route from primal MaxEnt
optimality to exponential-family RN form. No extra bundled certificate layer
is kept in the stable surface.
-/

/--
Finite-support duality API (unbundled):
if constraints are indexed by a finite support `index`, weak/strong duality plus
an equality-to-exponential bridge imply exponential RN form at any MaxEnt optimum.
-/
theorem IsMaxEntSolution.hasExponentialRNForm_of_finiteSupportDuality
    {μ₀ : Measure Ω}
    {index : Finset (LinearConstraint Ω)}
    (dualObjective : (index → ℝ) → ℝ≥0∞)
    (strongDualityAtOpt :
      ∀ {P : ACProbMeasure μ₀},
        IsMaxEntSolution (μ₀ := μ₀) (index : Set (LinearConstraint Ω)) P →
          ∃ Λ : index → ℝ, Objective (μ₀ := μ₀) P = dualObjective Λ)
    (equalityImpliesExponential :
      ∀ {P : ACProbMeasure μ₀} {Λ : index → ℝ},
        P ∈ Feasible (μ₀ := μ₀) (index : Set (LinearConstraint Ω)) →
          Objective (μ₀ := μ₀) P = dualObjective Λ →
            HasExponentialRNForm μ₀ index Λ P)
    {P : ACProbMeasure μ₀}
    (hP : IsMaxEntSolution (μ₀ := μ₀) (index : Set (LinearConstraint Ω)) P) :
    ∃ Λ : index → ℝ, HasExponentialRNForm μ₀ index Λ P := by
  rcases strongDualityAtOpt hP with ⟨Λ, hEq⟩
  exact ⟨Λ, equalityImpliesExponential hP.1 hEq⟩

end InfoGeometry.MaxEnt
