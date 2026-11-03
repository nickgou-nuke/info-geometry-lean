/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentParity

/-!
# Graded operator Hom spaces from tripotent zero-mode cuts

Dependency order: tripotent -> zero-mode reflection -> Hom involution ->
composition and evaluation compatibility -> homogeneous operator actions.
All maps are genuine real-linear operators; no commutativity of operators
or diagonal representation is imposed.

Composition supplies the left/right endomorphism actions on Hom(V,W).
This is the operator pairing layer only: no balanced tensor-product
isomorphism or graded Morita equivalence is asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Physics.Algebra

noncomputable section

variable {V W U : Type*}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W]
variable [AddCommGroup U] [Module ℝ U]

/-- The existing zero-mode reflection acting on the actual module. -/
abbrev moduleReflection (T : Module.End ℝ V) : Module.End ℝ V :=
  invS (projZero T)

theorem moduleReflection_apply_apply {T : Module.End ℝ V}
    (hT : T * T * T = T) (v : V) :
    moduleReflection T (moduleReflection T v) = v := by
  change (invS (projZero T) * invS (projZero T)) v = v
  rw [invS_projZero_sq hT]
  rfl

/-- Reflection on rectangular operator spaces; source and target cuts may differ. -/
def gradedHomParity (T : Module.End ℝ V) (S : Module.End ℝ W)
    (f : V →ₗ[ℝ] W) : V →ₗ[ℝ] W :=
  (moduleReflection S).comp (f.comp (moduleReflection T))

theorem gradedHomParity_involutive {T : Module.End ℝ V} {S : Module.End ℝ W}
    (hT : T * T * T = T) (hS : S * S * S = S) (f : V →ₗ[ℝ] W) :
    gradedHomParity T S (gradedHomParity T S f) = f := by
  ext v
  simp only [gradedHomParity, LinearMap.comp_apply, moduleReflection_apply_apply hT,
    moduleReflection_apply_apply hS]

/-- The intermediate reflection cancels in operator composition. -/
theorem gradedHomParity_comp {S : Module.End ℝ W}
    (hS : S * S * S = S) (T : Module.End ℝ V) (R : Module.End ℝ U)
    (g : W →ₗ[ℝ] U) (f : V →ₗ[ℝ] W) :
    gradedHomParity T R (g.comp f) =
      (gradedHomParity S R g).comp (gradedHomParity T S f) := by
  ext v
  simp only [gradedHomParity, LinearMap.comp_apply, moduleReflection_apply_apply hS]

/-- Evaluation intertwines the operator and module parity actions. -/
theorem gradedHomParity_eval {T : Module.End ℝ V}
    (hT : T * T * T = T) (S : Module.End ℝ W) (f : V →ₗ[ℝ] W) (v : V) :
    gradedHomParity T S f (moduleReflection T v) = moduleReflection S (f v) := by
  simp only [gradedHomParity, LinearMap.comp_apply, moduleReflection_apply_apply hT]

theorem gradedHomParity_id {T : Module.End ℝ V} (hT : T * T * T = T) :
    gradedHomParity T T LinearMap.id = LinearMap.id := by
  ext v
  simpa only [gradedHomParity, LinearMap.comp_apply, LinearMap.id_apply] using
    moduleReflection_apply_apply hT v

/-- An even operator is exactly an intertwiner of the two module reflections. -/
theorem gradedHomParity_even_iff {T : Module.End ℝ V}
    (hT : T * T * T = T) (S : Module.End ℝ W) (f : V →ₗ[ℝ] W) :
    gradedHomParity T S f = f ↔
      (moduleReflection S).comp f = f.comp (moduleReflection T) := by
  constructor
  · intro h
    ext v
    have hv := LinearMap.congr_fun h (moduleReflection T v)
    simpa only [gradedHomParity, LinearMap.comp_apply, moduleReflection_apply_apply hT] using hv
  · intro h
    ext v
    have hv := LinearMap.congr_fun h (moduleReflection T v)
    simpa only [gradedHomParity, LinearMap.comp_apply, moduleReflection_apply_apply hT] using hv

/-- Even morphisms compose without any commutativity hypothesis. -/
theorem gradedHomParity_even_comp {T : Module.End ℝ V} {S : Module.End ℝ W}
    {R : Module.End ℝ U} (hS : S * S * S = S)
    {g : W →ₗ[ℝ] U} {f : V →ₗ[ℝ] W}
    (hg : gradedHomParity S R g = g) (hf : gradedHomParity T S f = f) :
    gradedHomParity T R (g.comp f) = g.comp f := by
  rw [gradedHomParity_comp hS, hg, hf]

/-- The grading involution is an actual real-linear equivalence on each Hom
space, with itself as inverse. -/
noncomputable def gradedHomParityEquiv {T : Module.End ℝ V} {S : Module.End ℝ W}
    (hT : T * T * T = T) (hS : S * S * S = S) :
    (V →ₗ[ℝ] W) ≃ₗ[ℝ] (V →ₗ[ℝ] W) where
  toFun := gradedHomParity T S
  invFun := gradedHomParity T S
  left_inv := gradedHomParity_involutive hT hS
  right_inv := gradedHomParity_involutive hT hS
  map_add' f g := by ext v; simp [gradedHomParity]
  map_smul' r f := by ext v; simp [gradedHomParity]

/-- Both endomorphism actions on the rectangular Hom bimodule respect parity. -/
theorem gradedHomParity_bimodule {T : Module.End ℝ V} {S : Module.End ℝ W}
    (hT : T * T * T = T) (hS : S * S * S = S)
    (a : Module.End ℝ W) (f : V →ₗ[ℝ] W) (b : Module.End ℝ V) :
    gradedHomParity T S (a.comp (f.comp b)) =
      (gradedHomParity S S a).comp
        ((gradedHomParity T S f).comp (gradedHomParity T T b)) := by
  rw [gradedHomParity_comp hS, gradedHomParity_comp hT]

/-- Homogeneous operator composition multiplies the parity signs.
Specializing the signs to `1` and `-1` gives all four Z₂ product laws. -/
theorem gradedHomParity_homogeneous_comp {T : Module.End ℝ V} {S : Module.End ℝ W}
    {R : Module.End ℝ U} (hS : S * S * S = S)
    {g : W →ₗ[ℝ] U} {f : V →ₗ[ℝ] W} {a b : ℝ}
    (hg : gradedHomParity S R g = b • g)
    (hf : gradedHomParity T S f = a • f) :
    gradedHomParity T R (g.comp f) = (b * a) • (g.comp f) := by
  rw [gradedHomParity_comp hS, hg, hf]
  ext v
  simp [smul_smul]

/-- The odd-odd composition is even in the full noncommutative operator algebra. -/
theorem gradedHomParity_odd_comp_odd {T : Module.End ℝ V} {S : Module.End ℝ W}
    {R : Module.End ℝ U} (hS : S * S * S = S)
    {g : W →ₗ[ℝ] U} {f : V →ₗ[ℝ] W}
    (hg : gradedHomParity S R g = -g) (hf : gradedHomParity T S f = -f) :
    gradedHomParity T R (g.comp f) = g.comp f := by
  rw [gradedHomParity_comp hS, hg, hf]
  ext v
  simp

/-- On the endomorphism algebra this is the existing five-grade parity. -/
theorem gradedHomParity_end (T X : Module.End ℝ V) :
    gradedHomParity T T X = parityConj (projZero T) X := rfl

/-- Every native five-grade component acts with its derived parity sign. -/
theorem fiveGrade_module_action {T X : Module.End ℝ V}
    (hT : T * T * T = T) (k : FiveGrade) (hX : X ∈ fiveGradeRange T k) (v : V) :
    moduleReflection T (X v) =
      if k = .negOne ∨ k = .posOne then -(X (moduleReflection T v))
      else X (moduleReflection T v) := by
  have h := LinearMap.congr_fun
    (parityConj_projZero_of_mem_fiveGradeRange hT k hX) (moduleReflection T v)
  rw [← gradedHomParity_end, gradedHomParity_eval hT] at h
  split_ifs at h ⊢ <;> simpa using h

end
end InfoGeometry.OperatorAlgebra.PeirceSpine
