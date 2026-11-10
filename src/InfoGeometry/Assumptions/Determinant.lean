/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Architect
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Instances.Matrix

/-!
# Assumptions.Determinant

Determinant/group interface now aligned with mathlib objects:
- `GL` as `Matrix.GeneralLinearGroup` over any `[Ring R]`
- `detHom` as `Matrix.GeneralLinearGroup.det`
- `SL` as `Matrix.SpecialLinearGroup`
-/

namespace InfoGeometry.Assumptions.Determinant

universe u v

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem determinant_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- Canonical matrix general linear group over any (possibly noncommutative) `[Ring R]`. -/
abbrev «GL» (R : Type u) (V : Type v)
    [Ring R] [Fintype V] [DecidableEq V] :=
  Matrix.GeneralLinearGroup V R

/-- Right inverse law in `GL R V` over any noncommutative `[Ring R]`. -/
theorem gl_mul_inv (R : Type u) (V : Type v)
    [Ring R] [Fintype V] [DecidableEq V] (g : «GL» R V) :
    g * g⁻¹ = 1 :=
  mul_inv_cancel g

/-- Left inverse law in `GL R V` over any noncommutative `[Ring R]`. -/
theorem gl_inv_mul (R : Type u) (V : Type v)
    [Ring R] [Fintype V] [DecidableEq V] (g : «GL» R V) :
    g⁻¹ * g = 1 :=
  inv_mul_cancel g

/-- Determinant homomorphism `GL(V) →* Rˣ`. -/
noncomputable abbrev detHom (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    «GL» R V →* Rˣ :=
  Matrix.GeneralLinearGroup.det

/-- Canonical matrix special linear group. -/
abbrev «SL» (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    Type _ :=
  Matrix.SpecialLinearGroup V R

/-- Characterization of `SL` as determinant-1 matrices inside `GL`. -/
theorem ker_det_eq_SL (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    Set.range (Matrix.SpecialLinearGroup.toGL : «SL» R V → «GL» R V) =
      detHom R V ⁻¹' {1} := by
  ext x
  have h := (Matrix.SpecialLinearGroup.range_toGL_eq_ker_det (n := V) (R := R))
  have hmem := Subgroup.ext_iff.mp h x
  simpa [Subgroup.mem_carrier, MonoidHom.mem_range, MonoidHom.mem_ker, detHom] using hmem

/-- Draft logarithmic absolute determinant. -/
@[blueprint "def:determinant-log-abs"]
noncomputable def logAbsDet (V : Type v)
    [Fintype V] [DecidableEq V] : «GL» ℝ V → ℝ := fun g =>
  Real.log (|((detHom ℝ V g : ℝˣ) : ℝ)|)

/-- Jacobian determinant helper (`det` on linear automorphisms). -/
@[blueprint "def:determinant-jac"]
noncomputable abbrev jacDet (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V] :
    «GL» R V →* Rˣ :=
  detHom R V

/-- Jacobian chain rule for linear automorphisms. -/
theorem jacDet_comp (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V]
    (f g : «GL» R V) :
    jacDet R V (f * g) = jacDet R V f * jacDet R V g := by
  change detHom R V (f * g) = detHom R V f * detHom R V g
  exact (detHom R V).map_mul f g

/-- Named alias for multiplicative functoriality of the Jacobian determinant. -/
theorem jacobian_functoriality (R : Type u) (V : Type v)
    [CommRing R] [Fintype V] [DecidableEq V]
    (f g : «GL» R V) :
    jacDet R V (f * g) = jacDet R V f * jacDet R V g :=
  jacDet_comp R V f g

end InfoGeometry.Assumptions.Determinant
