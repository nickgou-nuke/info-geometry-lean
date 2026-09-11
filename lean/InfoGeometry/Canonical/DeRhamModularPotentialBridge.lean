import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Canonical.GrothendieckErlangenProjectiveBridge

/-!
# Finite Exact-Potential Shadow and de Rham Cohomology

This module records the finite groupoid analogue of an exact de Rham potential.
The coordinate `a : α` remains explicit: a relative modular potential is a
coordinate-valued transition function on positive rays.
-/

namespace InfoGeometry.Canonical.DeRhamModularPotentialBridge

open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.GrothendieckErlangenProjectiveBridge

universe u

variable {α : Type u}
variable [Fintype α] [Nonempty α]

abbrev StatisticalManifold (α : Type u) := PositiveRay α
abbrev ZeroForm (α : Type u) := StatisticalManifold α → α → ℝ
abbrev OneForm (α : Type u) := PositiveRay α → PositiveRay α → α → ℝ

/-- The scalar potential Φ_q(x) = V(q, x) is a 0-form. -/
noncomputable def scalarPotential_zeroForm (q : PositiveRay α) : ZeroForm α :=
  fun x a => relativeModularPotential q x a

/-- The discrete exterior derivative of a 0-form: (d₀ f)(x, x₀) = f(x₀) - f(x). -/
noncomputable def dZeroForm (f : ZeroForm α) : OneForm α :=
  fun x x₀ a => f x₀ a - f x a

/-- The modular potential V(x, x₀) is the exact 1-form dΦ_q. -/
theorem modularPotential_is_exact_oneForm (q x x₀ : PositiveRay α) :
    relativeModularPotential x x₀ =
      dZeroForm (scalarPotential_zeroForm q) x x₀ := by
  funext a
  dsimp [dZeroForm, scalarPotential_zeroForm]
  linarith [relativeModularPotential_cocycle q x x₀ a]

/-- The discrete exterior derivative of a 1-form on a 2-simplex:
    (d₁ ω)(x, x₀, x₁) = ω(x₀, x₁) - ω(x, x₁) + ω(x, x₀). -/
noncomputable def dOneForm (ω : OneForm α) :
    PositiveRay α → PositiveRay α → PositiveRay α → α → ℝ :=
  fun x x₀ x₁ a => ω x₀ x₁ a - ω x x₁ a + ω x x₀ a

/- d² = 0 is purely algebraic and does not use the finite-ray instances. -/
omit [Fintype α] [Nonempty α] in
theorem discrete_exterior_derivative_sq_zero (f : ZeroForm α)
    (x x₀ x₁ : PositiveRay α) (a : α) :
    dOneForm (dZeroForm f) x x₀ x₁ a = 0 := by
  unfold dOneForm dZeroForm
  ring

/-- Antisymmetry: V(q₀, q) = -V(q, q₀). -/
theorem modularPotential_antisymm (q q₀ : PositiveRay α) :
    relativeModularPotential q₀ q =
      fun a => -relativeModularPotential q q₀ a := by
  funext a
  have h := relativeModularPotential_cocycle q q₀ q a
  simp only [relativeModularPotential_self] at h
  linarith

/-- Closed loop: V(q, q₀) + V(q₀, q) = 0. -/
theorem modularPotential_closed_loop (q q₀ : PositiveRay α) (a : α) :
    relativeModularPotential q q₀ a + relativeModularPotential q₀ q a = 0 := by
  have h_anti := congrFun (modularPotential_antisymm q q₀) a
  linarith

/-- Path independence: V(q, q₀) + V(q₀, q₁) = V(q, q₁). -/
theorem path_independence_of_exact_oneForm (q q₀ q₁ : PositiveRay α) (a : α) :
    relativeModularPotential q q₀ a + relativeModularPotential q₀ q₁ a =
      relativeModularPotential q q₁ a := by
  exact (relativeModularPotential_cocycle q q₀ q₁ a).symm

/-- A 1-form is closed if its d₁ is zero. -/
def IsClosedOneForm (ω : OneForm α) : Prop :=
  ∀ (x x₀ x₁ : PositiveRay α) (a : α), dOneForm ω x x₀ x₁ a = 0

/-- A 1-form is exact if it is the exterior derivative of a 0-form. -/
def IsExactOneForm (ω : OneForm α) : Prop :=
  ∃ f : ZeroForm α, ∀ x x₀, ω x x₀ = dZeroForm f x x₀

omit [Fintype α] [Nonempty α] in
theorem exact_oneForm_is_closed {ω : OneForm α}
    (hω : IsExactOneForm ω) : IsClosedOneForm ω := by
  rcases hω with ⟨f, hf⟩
  intro x x₀ x₁ a
  unfold dOneForm
  rw [hf x₀ x₁, hf x x₁, hf x x₀]
  exact discrete_exterior_derivative_sq_zero f x x₀ x₁ a

omit [Fintype α] [Nonempty α] in
theorem exact_oneForm_path_independence {ω : OneForm α}
    (hω : IsExactOneForm ω)
    (x x₀ x₁ : PositiveRay α) (a : α) :
    ω x x₁ a = ω x x₀ a + ω x₀ x₁ a := by
  have hclosed := exact_oneForm_is_closed hω x x₀ x₁ a
  unfold dOneForm at hclosed
  linarith

omit [Fintype α] [Nonempty α] in
theorem exact_oneForm_closed_loop {ω : OneForm α}
    (hω : IsExactOneForm ω)
    (x x₀ : PositiveRay α) (a : α) :
    ω x x₀ a + ω x₀ x a = 0 := by
  rcases hω with ⟨f, hf⟩
  rw [hf x x₀, hf x₀ x]
  simp [dZeroForm]

omit [Fintype α] [Nonempty α] in
theorem path_independence_to_exact_oneForm
    (base : PositiveRay α) {ω : OneForm α}
    (hpath : ∀ x x₀ x₁ a, ω x x₁ a = ω x x₀ a + ω x₀ x₁ a) :
    IsExactOneForm ω := by
  refine ⟨fun x a => ω base x a, ?_⟩
  intro x x₀
  funext a
  have h := hpath base x x₀ a
  unfold dZeroForm
  linarith

omit [Fintype α] [Nonempty α] in
theorem exact_oneForm_iff_path_independence
    (base : PositiveRay α) (ω : OneForm α) :
    IsExactOneForm ω ↔
      ∀ x x₀ x₁ a, ω x x₁ a = ω x x₀ a + ω x₀ x₁ a := by
  constructor
  · intro hω
    exact fun x x₀ x₁ a => exact_oneForm_path_independence hω x x₀ x₁ a
  · intro hpath
    exact path_independence_to_exact_oneForm base hpath

/-- The modular potential 1-form is closed. -/
theorem modularPotential_is_closed_oneForm :
    IsClosedOneForm (relativeModularPotential (α := α)) := by
  intro x x₀ x₁ a
  unfold dOneForm
  have h_cocycle := relativeModularPotential_cocycle x x₀ x₁ a
  linarith

/-- The modular potential 1-form is exact. -/
theorem modularPotential_is_exact_oneForm' (q : PositiveRay α) :
    IsExactOneForm (relativeModularPotential (α := α)) := by
  refine ⟨scalarPotential_zeroForm (α := α) q, ?_⟩
  intro x x₀
  exact modularPotential_is_exact_oneForm q x x₀

/-- The modular potential is both closed and exact (Poincaré Lemma). -/
theorem modular_potential_closed_and_exact (q : PositiveRay α) :
    IsClosedOneForm (relativeModularPotential (α := α)) ∧
      IsExactOneForm (relativeModularPotential (α := α)) :=
  ⟨modularPotential_is_closed_oneForm, modularPotential_is_exact_oneForm' q⟩

/-- The Gibbs distribution Δ = e^{-V} is the exponential map. -/
theorem gibbs_distribution_is_exponential_map
    (q q₀ : PositiveRay α) (a : α) :
    relativeDensity q q₀ a = Real.exp (-relativeModularPotential q q₀ a) := by
  rw [relativeDensity_eq_exp_relativeLogDensity]
  rw [relativeModularPotential_eq_neg_relativeLogDensity]
  ring_nf

/-- The modular Hamiltonian for a pair (q, q₀) is K = -V(q, q₀). -/
noncomputable def modularHamiltonian (q q₀ : PositiveRay α) : α → ℝ :=
  fun a => -relativeModularPotential q q₀ a

/-- The modular flow is the exponential of the modular Hamiltonian. -/
theorem modular_flow_is_exponential
    (q q₀ : PositiveRay α) (a : α) :
    relativeDensity q q₀ a = Real.exp (modularHamiltonian q q₀ a) := by
  unfold modularHamiltonian
  rw [relativeDensity_eq_exp_relativeLogDensity]
  rw [relativeModularPotential_eq_neg_relativeLogDensity]
  ring_nf

/-- The canonical dictionary of algebraic thermodynamics. -/
theorem canonical_dictionary_of_algebraic_thermodynamics :
    (∀ (q q₀ : PositiveRay α) (a : α), relativeModularPotential q₀ q a = -relativeModularPotential q q₀ a) ∧
    (∀ (q q₀ q₁ : PositiveRay α) (a : α), relativeModularPotential q q₁ a = relativeModularPotential q q₀ a + relativeModularPotential q₀ q₁ a) ∧
    (∀ (q q₀ : PositiveRay α) (a : α), relativeDensity q q₀ a = Real.exp (-relativeModularPotential q q₀ a)) :=
  ⟨fun q q₀ a => congrFun (modularPotential_antisymm q q₀) a,
   fun q q₀ q₁ a => relativeModularPotential_cocycle q q₀ q₁ a,
   fun q q₀ a => by
     rw [relativeDensity_eq_exp_relativeLogDensity]
     rw [relativeModularPotential_eq_neg_relativeLogDensity]
     ring_nf⟩

end InfoGeometry.Canonical.DeRhamModularPotentialBridge
