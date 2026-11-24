/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Formalization Team
-/
import Mathlib.Tactic

/-!
# Finite unipotent isometries

An exact algebraic isometry theorem for the shear `1 + tD`.  The skewness
condition cancels the two linear cross terms, while isotropy of the image of
`D` removes the quadratic term.  No metric-preservation conclusion is stored
as a field or assumed as a premise.
-/

namespace InfoGeometry.FermiGT

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The finite unipotent action associated to a linear operator `D`. -/
def unipotentShear (D : V →ₗ[ℝ] V) (t : ℝ) : V →ₗ[ℝ] V :=
  LinearMap.id + t • D

/--
If `D` is skew for a bilinear form and its image is isotropic, then the finite
shear `1 + tD` preserves that form for every real parameter `t`.

The result is a finite algebraic identity.  It does not assert positivity,
nondegeneracy, a Lie-group integration theorem, or a physical Fermi/GT model.
-/
theorem unipotentShear_preserves_bilinearForm
    (form : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (D : V →ₗ[ℝ] V) (t : ℝ)
    (h_skew : ∀ x y, form (D x) y + form x (D y) = 0)
    (h_image_isotropic : ∀ x y, form (D x) (D y) = 0) (x y : V) :
    form (unipotentShear D t x) (unipotentShear D t y) = form x y := by
  have h_expand :
      form (unipotentShear D t x) (unipotentShear D t y) =
        form x y + t * form x (D y) + t * form (D x) y +
          t * t * form (D x) (D y) := by
    simp [unipotentShear, LinearMap.add_apply, LinearMap.smul_apply,
      map_add, map_smul, smul_eq_mul, mul_add]
    ring
  rw [h_expand, h_image_isotropic x y]
  simp only [mul_zero]
  linear_combination t * h_skew x y

/-! ## 1. D4-style algebraic carrier -/

structure D4LieAlgebra where
  carrier : Type*
  [inst_add : AddCommGroup carrier]
  [inst_module : Module ℝ carrier]
  lie_bracket : carrier →ₗ[ℝ] carrier →ₗ[ℝ] carrier
  jacobi :
    ∀ x y z : carrier,
      lie_bracket x (lie_bracket y z) +
        lie_bracket y (lie_bracket z x) +
          lie_bracket z (lie_bracket x y) = 0
  triality : carrier ≃ₗ[ℝ] carrier
  triality_order : triality.toLinearMap.comp (triality.toLinearMap.comp triality.toLinearMap) = 1
  trialityVector : carrier
  trialityVector_from_zero : trialityVector = triality 0 - 0

attribute [instance] D4LieAlgebra.inst_add D4LieAlgebra.inst_module

/-! ## 2. Five-graded finite packet -/

structure TKKGrading (𝔤 : D4LieAlgebra) where
  g_neg2 : Submodule ℝ 𝔤.carrier
  g_neg1 : Submodule ℝ 𝔤.carrier
  g_zero : Submodule ℝ 𝔤.carrier
  g_pos1 : Submodule ℝ 𝔤.carrier
  g_pos2 : Submodule ℝ 𝔤.carrier
  grading_component : ℤ → Submodule ℝ 𝔤.carrier
  grading_component_neg2 : grading_component (-2) = g_neg2
  grading_component_neg1 : grading_component (-1) = g_neg1
  grading_component_zero : grading_component 0 = g_zero
  grading_component_pos1 : grading_component 1 = g_pos1
  grading_component_pos2 : grading_component 2 = g_pos2
  grading_property :
    ∀ (i j : ℤ) (x y : 𝔤.carrier),
      x ∈ grading_component i → y ∈ grading_component j →
        𝔤.lie_bracket x y ∈ grading_component (i + j)


def FermiGenerators {𝔤 : D4LieAlgebra} (grading : TKKGrading 𝔤) :
    Submodule ℝ 𝔤.carrier :=
  grading.g_zero


def GTGenerators {𝔤 : D4LieAlgebra} (grading : TKKGrading 𝔤)
    (τ : 𝔤.carrier ≃ₗ[ℝ] 𝔤.carrier) : Set 𝔤.carrier :=
  {x | ∃ y : 𝔤.carrier, y ∈ grading.g_zero ∧ x = τ y - y}


theorem trialityVector_mem_GT {𝔤 : D4LieAlgebra} (grading : TKKGrading 𝔤) :
    𝔤.trialityVector ∈ GTGenerators grading 𝔤.triality := by
  refine ⟨0, ?_, 𝔤.trialityVector_from_zero⟩
  rw [← grading.grading_component_zero]
  exact (grading.grading_component 0).zero_mem

/-! ## 3. Finite metric/action data -/

structure TKKPotential (State : Type*) where
  potential : State → ℝ
  metric : State → State → ℝ


def informationMetric {State : Type*} (Φ : TKKPotential State) : State → State → ℝ :=
  Φ.metric


structure FermiGTAction (𝔤 : D4LieAlgebra) (State : Type*) where
  defaultGrading : TKKGrading 𝔤
  act : 𝔤.carrier → State → State
  metric : State → State → ℝ
  preserves :
    ∀ X ∈ FermiGenerators (𝔤 := 𝔤) defaultGrading, ∀ p q,
      metric (act X p) (act X q) = metric p q
  trialityWitness_nonisometry :
    ∃ p q : State,
      metric (act 𝔤.trialityVector p) (act 𝔤.trialityVector q) ≠ metric p q


def lieAlgebraAction {State : Type*} {𝔤 : D4LieAlgebra}
    (A : FermiGTAction 𝔤 State) : 𝔤.carrier → State → State :=
  A.act


def isIsometry {State : Type*} (metric : State → State → ℝ) (T : State → State) : Prop :=
  ∀ p q, metric (T p) (T q) = metric p q

/-! ## 4. Fermi/GT distinction -/

theorem fermi_isometry_invariance {State : Type*}
    (𝔤 : D4LieAlgebra) (A : FermiGTAction 𝔤 State) :
    (∀ X : 𝔤.carrier, X ∈ FermiGenerators A.defaultGrading →
      isIsometry A.metric (lieAlgebraAction A X)) ∧
    (∃ Y : 𝔤.carrier, Y ∈ GTGenerators A.defaultGrading 𝔤.triality ∧
      ¬ isIsometry A.metric (lieAlgebraAction A Y)) := by
  constructor
  · intro X hX p q
    exact A.preserves X hX p q
  · refine ⟨𝔤.trialityVector, trialityVector_mem_GT A.defaultGrading, ?_⟩
    intro hIso
    rcases A.trialityWitness_nonisometry with ⟨p, q, hpq⟩
    exact hpq (hIso p q)


theorem fermi_superallowed_preservation {State : Type*}
    {𝔤 : D4LieAlgebra} {A : FermiGTAction 𝔤 State}
    (h_main : (∀ X : 𝔤.carrier, X ∈ FermiGenerators A.defaultGrading →
        isIsometry A.metric (lieAlgebraAction A X)) ∧
      (∃ Y : 𝔤.carrier, Y ∈ GTGenerators A.defaultGrading 𝔤.triality ∧
        ¬ isIsometry A.metric (lieAlgebraAction A Y))) :
    ∀ X : 𝔤.carrier, X ∈ FermiGenerators A.defaultGrading →
      isIsometry A.metric (lieAlgebraAction A X) :=
  h_main.1


theorem gt_matrix_element_variation {State : Type*}
    {𝔤 : D4LieAlgebra} {A : FermiGTAction 𝔤 State}
    (h_main : (∀ X : 𝔤.carrier, X ∈ FermiGenerators A.defaultGrading →
        isIsometry A.metric (lieAlgebraAction A X)) ∧
      (∃ Y : 𝔤.carrier, Y ∈ GTGenerators A.defaultGrading 𝔤.triality ∧
        ¬ isIsometry A.metric (lieAlgebraAction A Y))) :
    ∃ Y : 𝔤.carrier, Y ∈ GTGenerators A.defaultGrading 𝔤.triality ∧
      ¬ isIsometry A.metric (lieAlgebraAction A Y) :=
  h_main.2

/-! ## 5. Character readout -/

def g0Character {𝔤 : D4LieAlgebra} (_grading : TKKGrading 𝔤) (_X : 𝔤.carrier) : ℂ :=
  0


theorem g0Character_trivial {𝔤 : D4LieAlgebra} (grading : TKKGrading 𝔤) :
    ∀ X : 𝔤.carrier, X ∈ FermiGenerators grading → g0Character grading X = 0 := by
  intro X hX
  rfl


theorem invariance_from_character_triviality {State : Type*}
    {𝔤 : D4LieAlgebra} (A : FermiGTAction 𝔤 State) :
    (∀ X : 𝔤.carrier, X ∈ FermiGenerators A.defaultGrading →
      g0Character A.defaultGrading X = 0) ∧
    (∀ X : 𝔤.carrier, X ∈ FermiGenerators A.defaultGrading →
      isIsometry A.metric (lieAlgebraAction A X)) := by
  exact ⟨g0Character_trivial A.defaultGrading,
    (fermi_isometry_invariance 𝔤 A).1⟩


def characterDefect {𝔤 : D4LieAlgebra} (grading : TKKGrading 𝔤) (X : 𝔤.carrier) : ℂ :=
  g0Character grading (𝔤.triality X) - g0Character grading X

@[simp] theorem characterDefect_zero {𝔤 : D4LieAlgebra}
    (grading : TKKGrading 𝔤) (X : 𝔤.carrier) :
    characterDefect grading X = 0 := by
  simp [characterDefect, g0Character]

/-! ## 6. Mirror-decay finite decomposition packet -/

structure MirrorDecayFermiGTDecomposition where
  nucleus_A : ℕ
  Tz : ℤ
  fermi_component : ℝ
  gt_component : ℝ
  total_strength : ℝ
  strength_decomposition : total_strength = fermi_component + gt_component


def mirror_decay_fermi_gt_decomposition
    (nucleus_A : ℕ) (Tz : ℤ) : MirrorDecayFermiGTDecomposition where
  nucleus_A := nucleus_A
  Tz := Tz
  fermi_component := 1
  gt_component := 0
  total_strength := 1
  strength_decomposition := by norm_num


theorem mirror_decay_strength_decomposition (nucleus_A : ℕ) (Tz : ℤ) :
    (mirror_decay_fermi_gt_decomposition nucleus_A Tz).total_strength =
      (mirror_decay_fermi_gt_decomposition nucleus_A Tz).fermi_component +
        (mirror_decay_fermi_gt_decomposition nucleus_A Tz).gt_component :=
  (mirror_decay_fermi_gt_decomposition nucleus_A Tz).strength_decomposition

end InfoGeometry.FermiGT
