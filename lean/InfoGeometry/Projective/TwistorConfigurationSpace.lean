import Mathlib.Tactic
import InfoGeometry.Projective.ArnoldRelations

noncomputable section

/-!
# Twistor Configuration Space Scaffolding

This module introduces a conservative, Lean-checkable scaffold for
`F_Q(ℂ^4,3)`.

Current status:

* only finite algebraic definitions are provided (quadratic form and pairwise
  non-degeneracy);
* no heavy analytic/cohomological theorems are claimed yet;
* no physical identification is assumed.
-/

open scoped BigOperators

namespace InfoGeometry.Projective.TwistorConfigurationSpace

/-- 4-component complex vector carrier for the ambient space `\C^4`. -/
abbrev C4 : Type := Fin 4 → ℂ

/-- Ordered triple of points in `\C^4`. -/
abbrev TripleC4 : Type := Fin 3 → C4

/-- A quadratic form used for the formal separation function.

`q(x)=\sum_i x_i^2`.
This is a placeholder for the projective split-signature form used in the bridge
files.
-/
def quadForm (x : C4) : ℂ := ∑ i : Fin 4, x i ^ 2

/-- Quadratic separation of two points: `Q(x_i - x_j)`. -/
def quadSeparation (x y : C4) : ℂ := quadForm (x - y)

theorem quadSeparation_translate (x y t : C4) :
    quadSeparation (x + t) (y + t) = quadSeparation x y := by
  unfold quadSeparation quadForm
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem quadSeparation_smul (c : ℂ) (x y : C4) :
    quadSeparation (c • x) (c • y) = c ^ 2 * quadSeparation x y := by
  unfold quadSeparation quadForm
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_sub]
  simp_rw [mul_pow]
  rw [Finset.mul_sum]

theorem quadSeparation_comm (x y : C4) :
    quadSeparation x y = quadSeparation y x := by
  unfold quadSeparation quadForm
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.sub_apply]
  ring

/-- Pairwise non-isotropic configurations: all ordered pairs are off the quadric. -/
def PairwiseNonIsotropic (X : TripleC4) : Prop :=
  ∀ i j : Fin 3, i ≠ j → quadSeparation (X i) (X j) ≠ 0

/-- The open `C^4`-triple configuration space `F_Q(ℂ^4,3)` as a subtype. -/
structure FQ3 where
  points : TripleC4
  pairwiseNonIsotropic : PairwiseNonIsotropic points

-- Coercions are intentionally omitted; use `FQ3.points` explicitly where needed.

namespace FQ3

def permute (X : FQ3) (σ : Equiv.Perm (Fin 3)) : FQ3 :=
  ⟨fun i => X.points (σ i), by
    intro i j hij
    exact X.pairwiseNonIsotropic (σ i) (σ j) (σ.injective.ne hij)⟩

/-- Projection to the underlying triple of points. -/
def carrier (X : FQ3) : TripleC4 := X.points

/-- The pairwise separation for a configuration.

This is the formal slot for the factor by `Q(x_i - x_j) ≠ 0`.
-/
def separation (X : FQ3) (i j : Fin 3) : ℂ :=
  quadSeparation (X.points i) (X.points j)

/-- Pairwise non-isotropicity as a direct projection from the structure field. -/
theorem pairwise_non_isotropic (X : FQ3) :
    ∀ i j : Fin 3, i ≠ j → X.separation i j ≠ 0 :=
  X.pairwiseNonIsotropic

theorem separation_permute (X : FQ3) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (X.permute σ).separation i j = X.separation (σ i) (σ j) := rfl

/-- Canonical symbolic one-forms `ω_{ij}` in the finite Arnold-combinatorial
module used elsewhere for mixed-relation bookkeeping.

No analytic meaning is asserted here; this is a notation-safe interface.
-/
def formalLogForm (i j : Fin 3) :
    ExteriorAlgebra ℂ ((Fin 3 × Fin 3) →₀ ℂ) :=
  InfoGeometry.Projective.Amplituhedron.w ℂ (Fin 3) i j

end FQ3

end InfoGeometry.Projective.TwistorConfigurationSpace
