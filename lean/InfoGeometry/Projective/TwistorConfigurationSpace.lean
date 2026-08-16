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
This is the finite quadratic separation form used by this scaffold.  The file
does not identify it with a projective split-signature or conformal form.
-/
def quadForm (x : C4) : ℂ := ∑ i : Fin 4, x i ^ 2

theorem quadForm_neg (x : C4) :
    quadForm (-x) = quadForm x := by
  unfold quadForm
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem quadForm_zero : quadForm (0 : C4) = 0 := by
  simp [quadForm]

/-- Quadratic separation of two points: `Q(x_i - x_j)`. -/
def quadSeparation (x y : C4) : ℂ := quadForm (x - y)

theorem quadSeparation_self (x : C4) :
    quadSeparation x x = 0 := by
  simp [quadSeparation, quadForm_zero]

theorem quadSeparation_comm (x y : C4) :
    quadSeparation x y = quadSeparation y x := by
  have h : x - y = -(y - x) := by
    funext i
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  calc
    quadSeparation x y = quadForm (x - y) := rfl
    _ = quadForm (-(y - x)) := by rw [h]
    _ = quadForm (y - x) := quadForm_neg (y - x)
    _ = quadSeparation y x := rfl

theorem quadSeparation_translate (x y a : C4) :
    quadSeparation (x + a) (y + a) = quadSeparation x y := by
  have h : (x + a) - (y + a) = x - y := by
    funext i
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  calc
    quadSeparation (x + a) (y + a) =
        quadForm ((x + a) - (y + a)) := rfl
    _ = quadForm (x - y) := by rw [h]
    _ = quadSeparation x y := rfl

/-- Pairwise non-isotropic configurations: all ordered pairs are off the quadric. -/
def PairwiseNonIsotropic (X : TripleC4) : Prop :=
  ∀ i j : Fin 3, i ≠ j → quadSeparation (X i) (X j) ≠ 0

/-- The open `C^4`-triple configuration space `F_Q(ℂ^4,3)` as a subtype. -/
structure FQ3 where
  points : TripleC4
  pairwiseNonIsotropic : PairwiseNonIsotropic points

-- Coercions are intentionally omitted; use `FQ3.points` explicitly where needed.

namespace FQ3

/-- Projection to the underlying triple of points. -/
def carrier (X : FQ3) : TripleC4 := X.points

/-! Reindex an ordered configuration by a permutation of its three labels. -/
def permute (σ : Equiv.Perm (Fin 3)) (X : FQ3) : FQ3 where
  points := fun i => X.points (σ i)
  pairwiseNonIsotropic := by
    intro i j hij
    apply X.pairwiseNonIsotropic (σ i) (σ j)
    intro h
    exact hij (σ.injective h)

@[simp] theorem permute_points (σ : Equiv.Perm (Fin 3)) (X : FQ3)
    (i : Fin 3) :
    (permute σ X).points i = X.points (σ i) := rfl

theorem permute_pairwise_non_isotropic (σ : Equiv.Perm (Fin 3)) (X : FQ3) :
    PairwiseNonIsotropic (fun i => X.points (σ i)) := by
  intro i j hij
  apply X.pairwiseNonIsotropic (σ i) (σ j)
  intro h
  exact hij (σ.injective h)

@[simp] theorem permute_refl (X : FQ3) :
    permute (Equiv.refl (Fin 3)) X = X := by
  cases X with
  | mk points hpoints =>
      rfl

theorem permute_trans (σ τ : Equiv.Perm (Fin 3)) (X : FQ3) :
    permute σ (permute τ X) = permute (σ.trans τ) X := by
  cases X with
  | mk points hpoints =>
      rfl

/-- The pairwise separation for a configuration.

This is the formal slot for the factor by `Q(x_i - x_j) ≠ 0`.
-/
def separation (X : FQ3) (i j : Fin 3) : ℂ :=
  quadSeparation (X.points i) (X.points j)

@[simp] theorem separation_permute (σ : Equiv.Perm (Fin 3)) (X : FQ3)
    (i j : Fin 3) :
    separation (permute σ X) i j = separation X (σ i) (σ j) := rfl

/-- Pairwise non-isotropicity as a direct projection from the structure field. -/
theorem pairwise_non_isotropic (X : FQ3) :
    ∀ i j : Fin 3, i ≠ j → X.separation i j ≠ 0 :=
  X.pairwiseNonIsotropic

/-- Canonical symbolic one-forms `ω_{ij}` in the finite Arnold-combinatorial
module used elsewhere for mixed-relation bookkeeping.

No analytic meaning is asserted here; this is a notation-safe interface.
-/
def formalLogForm (i j : Fin 3) :
    ExteriorAlgebra ℂ ((Fin 3 × Fin 3) →₀ ℂ) :=
  InfoGeometry.Projective.Amplituhedron.w ℂ (Fin 3) i j

end FQ3

end InfoGeometry.Projective.TwistorConfigurationSpace
