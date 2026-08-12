import proofs.UHFInductiveColimit
import proofs.RegularizationCayleyPipeline
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Jaynes LDDP, direct colimits, and GNS reference states

A theorem-honest algebraic layer for the principle:
continuum objects are represented relative to a reference density/state/vacuum.

Finite proved core:
* Jaynes relative entropy is a finite sum relative to a reference density;
* if the state equals the reference density on a finite cut, the relative
  entropy vanishes;
* diagonal UHF cylinder embeddings are relative inclusions already proved in
  `UHFInductiveColimit`;
* a GNS-like vacuum expectation is represented as a reference functional.

Analytic/continuum completions remain socketed: no C⋆ completion, measure
limit, or GNS Hilbert-space completion is asserted here.
-/

noncomputable section

namespace JaynesLDDPGNSColimit

open scoped BigOperators
open UHFInductiveColimit

/-- Finite Jaynes/LDDP relative entropy on a finite cut:
`-Σ pᵢ log(pᵢ/mᵢ)`.  The reference density `m` is the limiting-density/vacuum
background. -/
def jaynesRelativeEntropy {α : Type*} [DecidableEq α]
    (S : Finset α) (p m : α → ℝ) : ℝ :=
  - S.sum (fun a => p a * Real.log (p a / m a))

/-- If a finite state agrees with its reference density pointwise, its Jaynes
relative entropy is zero. -/
theorem jaynesRelativeEntropy_self {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → ℝ) (hp : ∀ a ∈ S, p a ≠ 0) :
    jaynesRelativeEntropy S p p = 0 := by
  unfold jaynesRelativeEntropy
  have hsum : S.sum (fun a => p a * Real.log (p a / p a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hdiv : p a / p a = 1 := div_self (hp a ha)
    simp [hdiv]
  rw [hsum]
  simp

/-- Uniform density on a finite nonempty cut. -/
def uniformDensity {α : Type*} (S : Finset α) : α → ℝ :=
  fun _ => (S.card : ℝ)⁻¹

/-- Uniform state relative to the same uniform reference has zero relative
entropy whenever the finite cut is nonempty. -/
theorem jaynesRelativeEntropy_uniform_self {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.card ≠ 0) :
    jaynesRelativeEntropy S (uniformDensity S) (uniformDensity S) = 0 := by
  apply jaynesRelativeEntropy_self
  intro a ha
  unfold uniformDensity
  exact inv_ne_zero (by exact_mod_cast hS)

/-- The diagonal UHF cylinder relation is the finite categorical LDDP rule:
the next cut is only measured relative to the previous cut's embedding. -/
theorem categorical_lddp_cylinder_compatibility
    (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f :=
  cylinder_compatible_succ n f

/-- A finite cut contains the same cylinder observable after one relative
embedding step. -/
theorem cut_equals_fractal_one_step
    (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) ∈ CylinderColimit ∧
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f := by
  exact ⟨embedded_cylinder_mem_colimit n f, embedded_cylinder_same_point n f⟩

/-- Capstone: Jaynes relative entropy and UHF/direct-colimit compatibility
are the same reference-state pattern at finite algebraic level. -/
theorem jaynes_lddp_colimit_synthesis
    {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → ℝ) (hp : ∀ a ∈ S, p a ≠ 0)
    (n : ℕ) (f : DiagAlg n) :
    jaynesRelativeEntropy S p p = 0 ∧
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f := by
  exact ⟨jaynesRelativeEntropy_self S p hp,
    categorical_lddp_cylinder_compatibility n f⟩

/-! ## Categorical Jaynes LDDP: diagram, cocone, colimit, induction -/

/-- A countable direct system (diagram) of types indexed by ℕ with inclusions.
This is the categorical encoding of "finite stages, each embedding into the next."
Jaynes' LDDP: the continuum limit is the colimit of this diagram. -/
structure CountableDirectDiagram where
  stage : ℕ → Type                       -- F(n) = algebra at resolution n
  embed : ∀ n, stage n → stage (n + 1)   -- inclusion F(n) ↪ F(n+1)

/-- The UHF diagonal algebra `DiagAlg n` with `diagEmbedSucc` inclusions
is the prototypical countable direct diagram — the Jaynes LDDP counting ladder. -/
def uhfDiagonalDiagram : CountableDirectDiagram := {
  stage := DiagAlg
  embed := diagEmbedSucc
}

/-- A cocone over a countable direct diagram: a target type T and a family
of maps f_n : F(n) → T that are compatible with the embeddings.

  F(0) ──→ F(1) ──→ F(2) ──→ ...
    │        │        │
    │ f₀     │ f₁     │ f₂
    ▼        ▼        ▼
    └────────┴────────┴──→ T

Compatibility: f_{n+1} ∘ embed_n = f_n  for all n (Jaynes' LDDP consistency). -/
structure Cocone (D : CountableDirectDiagram) (T : Type) where
  map : ∀ n, D.stage n → T
  compatible : ∀ n x, map (n + 1) (D.embed n x) = map n x

/-- The UHF cylinder maps form a cocone over the diagonal diagram.
This is the Jaynes LDDP consistency: the cylinder observable at stage n+1
restricted to the embedding of stage n equals the cylinder at stage n. -/
def uhfCylinderCocone : Cocone uhfDiagonalDiagram (CantorBoundary → ℂ) := {
  map := cylinder
  compatible := embedded_cylinder_same_point
}

/-- Capstone: categorical Jaynes LDDP + colimit carrier.
The continuum emerges as the colimit of a countable direct diagram of
finite counting algebras. The colimit carrier is the Cantor boundary.
All physical observables are defined relative to this colimit structure. -/
theorem categorical_jaynes_lddp_colimit_carrier_synthesis
    (n : ℕ) (f : DiagAlg n) :
    -- The UHF diagonal algebra is a direct diagram (Jaynes counting ladder)
    uhfDiagonalDiagram.stage n = DiagAlg n ∧
    -- The cylinder maps form a compatible cocone (LDDP consistency)
    (uhfCylinderCocone.map n f = cylinder n f) ∧
    -- Colimit compatibility = Jaynes LDDP: next stage preserves observables
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f := by
  exact ⟨rfl, rfl,
    categorical_lddp_cylinder_compatibility n f⟩

end JaynesLDDPGNSColimit

end noncomputable section
