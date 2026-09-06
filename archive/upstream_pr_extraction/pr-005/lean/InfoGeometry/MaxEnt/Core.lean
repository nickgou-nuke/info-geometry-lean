import InfoGeometry.KL.Measure

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

lemma SatisfiesIntegrable.integrable
    {μ : Measure Ω} {C : LinearConstraint Ω}
    (hC : SatisfiesIntegrable (μ := μ) C) :
    IntegrableUnder (μ := μ) C :=
  hC.1

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

lemma FeasibleIntegrable_subset_Feasible
    (constraints : Set (LinearConstraint Ω)) :
    FeasibleIntegrable (μ₀ := μ₀) constraints ⊆ Feasible (μ₀ := μ₀) constraints := by
  intro P hP C hC
  exact (hP C hC).satisfies

lemma ConstraintsIntegrableOn_of_memFeasibleIntegrable
    (constraints : Set (LinearConstraint Ω))
    {P : ACProbMeasure μ₀}
    (hP : P ∈ FeasibleIntegrable (μ₀ := μ₀) constraints) :
    ConstraintsIntegrableOn (μ := P.μ) constraints := by
  intro C hC
  exact (hP C hC).integrable

/-- KL objective over the feasible set. -/
noncomputable def Objective (P : ACProbMeasure μ₀) : ℝ≥0∞ :=
  InfoGeometry.KL.klDiv P.μ μ₀

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
## Dual/Fenchel Interface (Structural)

This section packages the assumptions typically needed to pass from primal
MaxEnt optimality to exponential-family RN form via a Fenchel-duality route.
-/

/-- Assumptions for deriving exponential RN form from Fenchel duality. -/
structure FenchelDualAssumptions
    (μ₀ : Measure Ω)
    (constraints : Set (LinearConstraint Ω))
    (index : Finset (LinearConstraint Ω)) where
  /-- The finite index family exactly represents the ambient constraint set. -/
  index_exact : ∀ C, C ∈ constraints ↔ C ∈ index
  /-- Abstract dual objective functional (kept structural at this layer). -/
  dualObjective : (index → ℝ) → ℝ≥0∞
  /-- Weak duality: dual value lower-bounds every feasible primal value. -/
  weakDuality :
    ∀ {P : ACProbMeasure μ₀},
      P ∈ Feasible (μ₀ := μ₀) constraints →
        ∀ Λ : index → ℝ,
          dualObjective Λ ≤ Objective (μ₀ := μ₀) P
  /-- Strong duality at an optimal primal point. -/
  strongDualityAtOpt :
    ∀ {P : ACProbMeasure μ₀},
      IsMaxEntSolution (μ₀ := μ₀) constraints P →
        ∃ Λ : index → ℝ, Objective (μ₀ := μ₀) P = dualObjective Λ
  /-- Equality case bridge to exponential-form RN density. -/
  equalityImpliesExponential :
    ∀ {P : ACProbMeasure μ₀} {Λ : index → ℝ},
      P ∈ Feasible (μ₀ := μ₀) constraints →
        Objective (μ₀ := μ₀) P = dualObjective Λ →
          HasExponentialRNForm μ₀ index Λ P

/-- Fenchel-duality skeleton:
MaxEnt optimality implies exponential RN form under explicit dual assumptions. -/
theorem IsMaxEntSolution.hasExponentialRNForm_of_fenchel
    {μ₀ : Measure Ω}
    {constraints : Set (LinearConstraint Ω)}
    {index : Finset (LinearConstraint Ω)}
    (hFenchel : FenchelDualAssumptions μ₀ constraints index)
    {P : ACProbMeasure μ₀}
    (hP : IsMaxEntSolution (μ₀ := μ₀) constraints P) :
    ∃ Λ : index → ℝ, HasExponentialRNForm μ₀ index Λ P := by
  rcases hFenchel.strongDualityAtOpt hP with ⟨Λ, hEq⟩
  exact ⟨Λ, hFenchel.equalityImpliesExponential hP.1 hEq⟩

end InfoGeometry.MaxEnt
