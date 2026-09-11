import InfoGeometry.External.Auto.UHFInductiveColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite Jaynes relative entropy and UHF cylinder compatibility

This module contains the finite theorem-backed core of the proposed
Jaynes/LDDP/GNS-colimit picture:

* finite Jaynes relative entropy is defined relative to a reference density;
* self-relative entropy vanishes when the density is nonzero on the cut;
* UHF diagonal cylinder observables are preserved by the existing successor
  embedding.
-/

noncomputable section

namespace JaynesLDDPGNSColimit

open scoped BigOperators
open UHFInductiveColimit

/-- Finite Jaynes relative entropy on a finite cut: `-Σ pᵢ log(pᵢ/mᵢ)`. -/
def jaynesRelativeEntropy {α : Type*} [DecidableEq α]
    (S : Finset α) (p m : α → ℝ) : ℝ :=
  -S.sum fun a => p a * Real.log (p a / m a)

/-- A finite state has zero entropy relative to itself when it is nonzero on
the selected cut. -/
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

/-- Uniform density on a finite cut. -/
def uniformDensity {α : Type*} (S : Finset α) : α → ℝ :=
  fun _ => (S.card : ℝ)⁻¹

/-- A nonempty finite uniform density has zero entropy relative to itself. -/
theorem jaynesRelativeEntropy_uniform_self {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : S.card ≠ 0) :
    jaynesRelativeEntropy S (uniformDensity S) (uniformDensity S) = 0 := by
  apply jaynesRelativeEntropy_self
  intro _ _
  unfold uniformDensity
  exact inv_ne_zero (by exact_mod_cast hS)

/-- The successor diagonal embedding preserves its cylinder observable. -/
theorem categorical_lddp_cylinder_compatibility
    (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f :=
  cylinder_compatible_succ n f

/-- The embedded cylinder is a member of the concrete cylinder union and
represents the same observable as at the preceding stage. -/
theorem cut_equals_fractal_one_step
    (n : ℕ) (f : DiagAlg n) :
    cylinder (n + 1) (diagEmbedSucc n f) ∈ CylinderColimit ∧
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f :=
  ⟨embedded_cylinder_mem_colimit n f, embedded_cylinder_same_point n f⟩

/-- Finite synthesis of self-relative entropy and UHF successor compatibility.
This is not a categorical-colimit or GNS-completion theorem. -/
theorem jaynes_lddp_colimit_synthesis
    {α : Type*} [DecidableEq α]
    (S : Finset α) (p : α → ℝ) (hp : ∀ a ∈ S, p a ≠ 0)
    (n : ℕ) (f : DiagAlg n) :
    jaynesRelativeEntropy S p p = 0 ∧
    cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f :=
  ⟨jaynesRelativeEntropy_self S p hp,
    categorical_lddp_cylinder_compatibility n f⟩

end JaynesLDDPGNSColimit

end noncomputable section
