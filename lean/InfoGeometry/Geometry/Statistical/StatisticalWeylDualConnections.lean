/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity
import InfoGeometry.Modular.AmariChentsovDualConnections

/-!
# The pure-trace obstruction on the existing dual-connection owner

This module puts the existing `DualConnectionManifold.g` into Mathlib's
native bilinear-form carrier and derives nondegeneracy from its positive
definiteness. The algebraic rigidity theorem then applies to the owner's
actual `amariCubicForm`.

First-two-slot cubic symmetry is an explicit hypothesis: the existing
`DualConnectionManifold` interface does not include torsion-free connections
or a theorem supplying that symmetry. Under this hypothesis, a pure-trace
factorization in dimension at least two forces the one-form to vanish and
the two connection maps to agree. This is a pointwise algebraic statement;
no manifold, curvature, or Levi-Civita uniqueness claim is asserted.
-/

namespace InfoGeometry.Geometry.Statistical.StatisticalWeylDualConnections

open InfoGeometry.Geometry.Statistical.StatisticalWeylRigidity
open InfoGeometry.Modular.AmariChentsovDualConnections

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The existing metric, expressed as a native bilinear form. -/
def metricBilinForm (M : DualConnectionManifold V) : LinearMap.BilinForm ℝ V where
  toFun x :=
    { toFun := M.g x
      map_add' := M.g_add_right x
      map_smul' := fun r y => M.g_smul_right r x y }
  map_add' x y := by
    ext z
    exact M.g_add_left x y z
  map_smul' r x := by
    ext y
    exact M.g_smul_left r x y

@[simp] theorem metricBilinForm_apply (M : DualConnectionManifold V) (x y : V) :
    metricBilinForm M x y = M.g x y := rfl

/-- Positive definiteness supplies both separating conditions of native nondegeneracy. -/
theorem metricBilinForm_nondegenerate (M : DualConnectionManifold V) :
    (metricBilinForm M).Nondegenerate := by
  constructor
  · intro x hx
    by_contra hne
    have hzero : M.g x x = 0 := hx x
    exact (M.g_pos_def x hne).ne' hzero
  · intro y hy
    by_contra hne
    have hzero : M.g y y = 0 := hy y
    exact (M.g_pos_def y hne).ne' hzero

/-- The owner's cubic form cannot be a nonzero pure Weyl trace in dimension at least two
when its first two slots are symmetric. -/
theorem cubic_pureTrace_oneForm_eq_zero
    (M : DualConnectionManifold V) (ω : V →ₗ[ℝ] ℝ)
    (hdim : 2 ≤ Module.finrank ℝ V)
    (hsym : ∀ x y z : V, amariCubicForm M x y z = amariCubicForm M y x z)
    (htrace : ∀ x y z : V, amariCubicForm M x y z = ω x * M.g y z) :
    ω = 0 := by
  apply pureTrace_symmetry_oneForm_eq_zero (metricBilinForm M)
    (metricBilinForm_nondegenerate M) ω hdim
  intro x y z
  exact (htrace x y z).symm.trans ((hsym x y z).trans (htrace y x z))

/-- Vanishing of the actual cubic difference, together with nondegeneracy,
forces the mixture and exponential connection maps to coincide. -/
theorem cubic_pureTrace_connections_eq
    (M : DualConnectionManifold V) (ω : V →ₗ[ℝ] ℝ)
    (hdim : 2 ≤ Module.finrank ℝ V)
    (hsym : ∀ x y z : V, amariCubicForm M x y z = amariCubicForm M y x z)
    (htrace : ∀ x y z : V, amariCubicForm M x y z = ω x * M.g y z)
    (x y : V) : M.nabla_m x y = M.nabla_e x y := by
  have hω := cubic_pureTrace_oneForm_eq_zero M ω hdim hsym htrace
  apply sub_eq_zero.mp
  apply (metricBilinForm_nondegenerate M).1
  intro z
  change amariCubicForm M x y z = 0
  rw [htrace, hω]
  simp

end InfoGeometry.Geometry.Statistical.StatisticalWeylDualConnections
