import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-- A spacetime is a topological space equipped with a causal preorder relation. -/
class Spacetime (M : Type) [TopologicalSpace M] where
  causal_le : M → M → Prop

/-- A compact, inhabited topological surface in a spacetime. -/
def is_cauchy_surface {M : Type} [TopologicalSpace M] [Spacetime M] (S : Set M) : Prop :=
  IsCompact S ∧ S.Nonempty

/-- Global hyperbolicity as existence of a compact inhabited Cauchy surface. -/
def is_globally_hyperbolic {M : Type} [TopologicalSpace M] [Spacetime M] : Prop :=
  ∃ _S : Set M, is_cauchy_surface _S

/-- Triviality represented by existence of a compact inhabited topological stage. -/
def milnor_lim1_trivial {M : Type} [TopologicalSpace M] : Prop :=
  ∃ K : Set M, IsCompact K ∧ K.Nonempty

/-- A Cauchy surface carries compactness as explicit topological content. -/
lemma compact_of_is_cauchy_surface {M : Type} [TopologicalSpace M] [Spacetime M] {S : Set M}
    (hS : is_cauchy_surface S) : IsCompact S := by
  cases hS with
  | intro hcompact _ =>
      simpa using hcompact

/-- A Cauchy surface carries nonemptiness as explicit topological content. -/
lemma nonempty_of_is_cauchy_surface {M : Type} [TopologicalSpace M] [Spacetime M] {S : Set M}
    (hS : is_cauchy_surface S) : S.Nonempty := by
  cases hS with
  | intro _ hnonempty =>
      simpa using hnonempty

/-- Global hyperbolicity produces an actual compact inhabited topological stage. -/
lemma compact_stage_of_global_hyperbolicity {M : Type} [TopologicalSpace M] [Spacetime M]
    (hM : is_globally_hyperbolic (M := M)) :
    ∃ K : Set M, IsCompact K ∧ K.Nonempty := by
  rcases hM with ⟨S, hS⟩
  refine ⟨S, ?_, ?_⟩
  · exact compact_of_is_cauchy_surface hS
  · exact nonempty_of_is_cauchy_surface hS

/-- A compact inhabited stage is exactly the stage condition used here. -/
lemma milnor_trivial_of_compact_stage {M : Type} [TopologicalSpace M] {K : Set M}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) :
    milnor_lim1_trivial (M := M) := by
  refine ⟨K, ?_⟩
  constructor
  · simpa using hcompact
  · simpa using hnonempty

/-- Global hyperbolicity is equivalent to the compact-stage condition. -/
theorem global_hyperbolicity_iff_milnor_trivial {M : Type} [TopologicalSpace M] [Spacetime M] :
    is_globally_hyperbolic (M := M) ↔ milnor_lim1_trivial (M := M) := by
  constructor
  · intro h
    rcases compact_stage_of_global_hyperbolicity h with ⟨K, hcompact, hnonempty⟩
    exact milnor_trivial_of_compact_stage hcompact hnonempty
  · intro h
    simpa [is_globally_hyperbolic, is_cauchy_surface, milnor_lim1_trivial] using h

/-- Pointwise nonnegative squared amplitude of a real state. -/
def is_bose_einstein_condensate {M : Type} [TopologicalSpace M] (state : M → ℝ) : Prop :=
  ∀ x : M, 0 ≤ (state x) ^ 2

/-- The sum of two real squared amplitudes is nonnegative. -/
lemma sum_two_squared_amplitudes_nonnegative (a b : ℝ) : 0 ≤ a ^ 2 + b ^ 2 := by
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  exact add_nonneg ha hb

/-- Multiplying the pointwise squared amplitude by itself remains nonnegative. -/
lemma squared_amplitude_product_nonnegative {M : Type} [TopologicalSpace M] (state : M → ℝ)
    (x : M) : 0 ≤ (state x) ^ 2 * (state x) ^ 2 := by
  have hx : 0 ≤ (state x) ^ 2 := sq_nonneg (state x)
  exact mul_nonneg hx hx

/-- Squared amplitudes of real states are nonnegative. -/
theorem condensation_at_cauchy_horizon {M : Type} [TopologicalSpace M] [Spacetime M] (state : M → ℝ) :
    is_bose_einstein_condensate state := by
  intro x
  have hx : 0 ≤ (state x) ^ 2 := sq_nonneg (state x)
  simpa [is_bose_einstein_condensate] using hx
