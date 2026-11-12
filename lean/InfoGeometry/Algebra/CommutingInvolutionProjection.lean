/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Averaging two commuting real linear involutions

The normalized four-term average is an actual linear projection. Its range
is the common fixed submodule, and its kernel is a complementary submodule.
No finite-dimensional hypothesis is needed.
-/

noncomputable section

namespace InfoGeometry.Algebra.CommutingInvolutionProjection

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The normalized average of the four words in two linear involutions. -/
def average (f g : M →ₗ[ℝ] M) : M →ₗ[ℝ] M :=
  (1 / 4 : ℝ) • (LinearMap.id + f + g + f.comp g)

theorem average_apply (f g : M →ₗ[ℝ] M) (x : M) :
    average f g x = (1 / 4 : ℝ) • (x + f x + g x + f (g x)) := rfl

/-- The joint fixed submodule uses the native kernels of the two differences. -/
def jointFixed (f g : M →ₗ[ℝ] M) : Submodule ℝ M :=
  LinearMap.ker (f - LinearMap.id) ⊓ LinearMap.ker (g - LinearMap.id)

theorem mem_jointFixed_iff (f g : M →ₗ[ℝ] M) (x : M) :
    x ∈ jointFixed f g ↔ f x = x ∧ g x = x := by
  simp [jointFixed, LinearMap.mem_ker, sub_eq_zero]

theorem first_average (f g : M →ₗ[ℝ] M)
    (hf : Function.Involutive f) (x : M) :
    f (average f g x) = average f g x := by
  simp only [average_apply, map_smul, map_add, hf]
  congr 1
  abel

theorem second_average (f g : M →ₗ[ℝ] M)
    (hg : Function.Involutive g) (hfg : Function.Commute f g) (x : M) :
    g (average f g x) = average f g x := by
  have hgf (y : M) : g (f y) = f (g y) := (hfg y).symm
  simp only [average_apply, map_smul, map_add, hgf, hg]
  congr 1
  abel

theorem average_of_fixed (f g : M →ₗ[ℝ] M) {x : M}
    (hf : f x = x) (hg : g x = x) : average f g x = x := by
  simp only [average_apply, hf, hg]
  module

theorem average_eq_self_iff (f g : M →ₗ[ℝ] M)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hfg : Function.Commute f g) (x : M) :
    average f g x = x ↔ f x = x ∧ g x = x := by
  constructor
  · intro hx
    exact ⟨hx ▸ first_average f g hf x, hx ▸ second_average f g hg hfg x⟩
  · rintro ⟨hfx, hgx⟩
    exact average_of_fixed f g hfx hgx

/-- The averaging endomorphism is idempotent under composition. -/
theorem average_isIdempotentElem (f g : M →ₗ[ℝ] M)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hfg : Function.Commute f g) : IsIdempotentElem (average f g) := by
  ext x
  exact average_of_fixed f g (first_average f g hf x) (second_average f g hg hfg x)

/-- Every joint fixed vector is attained, and every output is jointly fixed. -/
theorem range_average (f g : M →ₗ[ℝ] M)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hfg : Function.Commute f g) :
    LinearMap.range (average f g) = jointFixed f g := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (mem_jointFixed_iff f g _).mpr
      ⟨first_average f g hf y, second_average f g hg hfg y⟩
  · intro hx
    obtain ⟨hfx, hgx⟩ := (mem_jointFixed_iff f g x).mp hx
    exact ⟨x, average_of_fixed f g hfx hgx⟩

/-- The same projection with its actual fixed-submodule codomain. -/
def projection (f g : M →ₗ[ℝ] M)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hfg : Function.Commute f g) : M →ₗ[ℝ] jointFixed f g :=
  (average f g).codRestrict (jointFixed f g) fun x =>
    (mem_jointFixed_iff f g _).mpr
      ⟨first_average f g hf x, second_average f g hg hfg x⟩

theorem projection_fixed (f g : M →ₗ[ℝ] M)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hfg : Function.Commute f g) (x : jointFixed f g) :
    projection f g hf hg hfg x = x := by
  apply Subtype.ext
  exact average_of_fixed f g ((mem_jointFixed_iff f g x).mp x.property).1
    ((mem_jointFixed_iff f g x).mp x.property).2

/-- The range and kernel form a genuine complementary decomposition. -/
theorem jointFixed_isCompl_ker_projection (f g : M →ₗ[ℝ] M)
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (hfg : Function.Commute f g) :
    IsCompl (jointFixed f g) (LinearMap.ker (projection f g hf hg hfg)) :=
  LinearMap.isCompl_of_proj (projection_fixed f g hf hg hfg)

end InfoGeometry.Algebra.CommutingInvolutionProjection
