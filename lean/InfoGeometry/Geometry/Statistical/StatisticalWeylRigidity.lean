/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Basic.Real.Basic

/-!
# Symmetric pure-trace tensors and the statistical/Weyl obstruction

For a native real bilinear form `B` and a native one-form `ω`, consider the
pure-trace tensor `ω x * B y z`. Symmetry of its first two slots implies
`ω x • y = ω y • x` whenever `B` is nondegenerate. Consequently, a nonzero
`ω` forces every vector into the span of one vector. In dimension at least
two, `ω` must vanish.

No positivity or symmetry assumption on `B` is needed: left separation is
the part of native nondegeneracy consumed by the proof, so the result also
applies to nondegenerate indefinite metrics. The span statements are valid
without a prior finite-dimensionality assumption. A one-dimensional example
shows why the dimension restriction cannot be dropped.

This is a pointwise tensor theorem. It does not construct an affine connection,
a manifold, or an identification of statistical geometry with Weyl geometry.
-/

namespace InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Nondegeneracy turns symmetry of the pure-trace tensor into a vector identity. -/
theorem pureTrace_symmetry_smul_eq
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (ω : V →ₗ[ℝ] ℝ)
    (hsym : ∀ x y z : V, ω x * B y z = ω y * B x z)
    (x y : V) : ω x • y = ω y • x := by
  apply sub_eq_zero.mp
  apply hB.1
  intro z
  rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_left, hsym, sub_self]

/-- At any nonzero evaluation of the one-form, every vector is a specified multiple. -/
theorem pureTrace_symmetry_eq_smul
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (ω : V →ₗ[ℝ] ℝ)
    (hsym : ∀ x y z : V, ω x * B y z = ω y * B x z)
    (x : V) (hx : ω x ≠ 0) (y : V) :
    y = (ω y / ω x) • x := by
  have h := congrArg (fun v : V => (ω x)⁻¹ • v)
    (pureTrace_symmetry_smul_eq B hB ω hsym x y)
  simpa only [smul_smul, inv_mul_cancel₀ hx, one_smul,
    div_eq_mul_inv, mul_comm] using h

/-- Every vector lies in one native one-dimensional span. -/
theorem pureTrace_symmetry_mem_span
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (ω : V →ₗ[ℝ] ℝ)
    (hsym : ∀ x y z : V, ω x * B y z = ω y * B x z)
    (x : V) (hx : ω x ≠ 0) (y : V) :
    y ∈ Submodule.span ℝ ({x} : Set V) := by
  exact Submodule.mem_span_singleton.mpr
    ⟨ω y / ω x, (pureTrace_symmetry_eq_smul B hB ω hsym x hx y).symm⟩

/-- A nonzero evaluation makes that singleton span the entire vector space. -/
theorem pureTrace_symmetry_span_eq_top
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (ω : V →ₗ[ℝ] ℝ)
    (hsym : ∀ x y z : V, ω x * B y z = ω y * B x z)
    (x : V) (hx : ω x ≠ 0) :
    Submodule.span ℝ ({x} : Set V) = ⊤ := by
  apply top_unique
  intro y _
  exact pureTrace_symmetry_mem_span B hB ω hsym x hx y

/-- A nonzero one-form satisfying the symmetry condition forces dimension at most one. -/
theorem pureTrace_symmetry_finrank_le_one
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (ω : V →ₗ[ℝ] ℝ)
    (hsym : ∀ x y z : V, ω x * B y z = ω y * B x z)
    (hω : ω ≠ 0) : Module.finrank ℝ V ≤ 1 := by
  classical
  have hnot : ¬ ∀ x : V, ω x = 0 := by
    intro hzero
    apply hω
    ext x
    exact hzero x
  obtain ⟨x, hx⟩ := not_forall.mp hnot
  apply _root_.finrank_le_one x
  intro y
  exact ⟨ω y / ω x, (pureTrace_symmetry_eq_smul B hB ω hsym x hx y).symm⟩

/-- Statistical first-slot symmetry is incompatible with a nonzero pure Weyl trace
in dimension at least two, including for nondegenerate indefinite forms. -/
theorem pureTrace_symmetry_oneForm_eq_zero
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (ω : V →ₗ[ℝ] ℝ)
    (hdim : 2 ≤ Module.finrank ℝ V)
    (hsym : ∀ x y z : V, ω x * B y z = ω y * B x z) :
    ω = 0 := by
  by_contra hω
  have hle := pureTrace_symmetry_finrank_le_one B hB ω hsym hω
  exact (Nat.not_succ_le_self 1) (hdim.trans hle)

/-- The exact compatibility criterion on a vector space of dimension at least two. -/
theorem pureTrace_symmetric_iff_oneForm_eq_zero
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (ω : V →ₗ[ℝ] ℝ) (hdim : 2 ≤ Module.finrank ℝ V) :
    (∀ x y z : V, ω x * B y z = ω y * B x z) ↔ ω = 0 := by
  constructor
  · exact pureTrace_symmetry_oneForm_eq_zero B hB ω hdim
  · rintro rfl
    simp

/-- In dimension one, multiplication and the identity one-form give a genuine
nonzero symmetric pure-trace example with a nondegenerate native bilinear form. -/
theorem one_dimensional_nonzero_example :
    ∃ (B : LinearMap.BilinForm ℝ ℝ) (ω : ℝ →ₗ[ℝ] ℝ),
      B.Nondegenerate ∧ ω ≠ 0 ∧
        (∀ x y z : ℝ, ω x * B y z = ω y * B x z) ∧
        Module.finrank ℝ ℝ = 1 := by
  refine ⟨LinearMap.mul ℝ ℝ, LinearMap.id, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro x hx
      simpa only [LinearMap.mul_apply', mul_one] using hx 1
    · intro y hy
      simpa only [LinearMap.mul_apply', one_mul] using hy 1
  · intro h
    have hh := congrArg (fun f : ℝ →ₗ[ℝ] ℝ => f 1) h
    exact (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa using hh)
  · intro x y z
    change x * (y * z) = y * (x * z)
    exact mul_left_comm x y z
  · exact Module.finrank_self ℝ

end InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity
