/- 
InfoGeometry/ProjectiveFoundation.lean

Real projective substrate for the modular bridge.

This is the core geometric layer:
- the substrate is real, not complex;
- the projective symmetry is treated separately from the lifted cocycle;
- cusp behavior is only a filter statement;
- the complex upper-half-plane model is reserved for later comparison files.
-/

import Mathlib.Algebra.Group.Action.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Center
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic
import InfoGeometry.Geometry.RealMoebiusAction
import InfoGeometry.Geometry.RealUpperHalfPlane

noncomputable section

open scoped MatrixGroups Topology
open Filter
open InfoGeometry.Geometry

namespace InfoGeometry.ProjectiveFoundation

abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ
abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ

abbrev PSL2R := Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ
abbrev PSL2Z := Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℤ

/-- The quotient map from the cover to the projective group. -/
abbrev sl2rToPSL2R : SL2R →* PSL2R :=
  QuotientGroup.mk' (Subgroup.center SL2R)

/-- The arithmetic quotient map from the integral cover to the projective group. -/
abbrev sl2zToPSL2Z : SL2Z →* PSL2Z :=
  QuotientGroup.mk' (Subgroup.center SL2Z)

/--
A rotor cocycle represented on a cover.

`Γgeom` acts on the real base space `X`.
`Γcover` is a lift/cover of `Γgeom`.
The cocycle is evaluated on the cover, but the base point is moved by the
projected geometric action.

This is the correct home of spin signs and multiplier anomalies.
-/
structure CoverRotorCocycle
    (Γcover Γgeom X R : Type*)
    [Group Γcover] [Group Γgeom] [MulAction Γgeom X] [Group R] where
  projection : Γcover →* Γgeom
  toFun : Γcover → X → R
  map_one' : ∀ x : X, toFun 1 x = 1
  map_mul' : ∀ γ δ x,
    toFun (γ * δ) x =
      toFun γ ((projection δ) • x) * toFun δ x

instance
    {Γcover Γgeom X R : Type*}
    [Group Γcover] [Group Γgeom] [MulAction Γgeom X] [Group R] :
    CoeFun (CoverRotorCocycle Γcover Γgeom X R)
      (fun _ => Γcover → X → R) where
  coe C := C.toFun

@[simp]
theorem CoverRotorCocycle.map_one
    {Γcover Γgeom X R : Type*}
    [Group Γcover] [Group Γgeom] [MulAction Γgeom X] [Group R]
    (C : CoverRotorCocycle Γcover Γgeom X R)
    (x : X) :
    C 1 x = 1 :=
  C.map_one' x

@[simp]
theorem CoverRotorCocycle.map_mul
    {Γcover Γgeom X R : Type*}
    [Group Γcover] [Group Γgeom] [MulAction Γgeom X] [Group R]
    (C : CoverRotorCocycle Γcover Γgeom X R)
    (γ δ : Γcover)
    (x : X) :
    C (γ * δ) x =
      C γ ((C.projection δ) • x) * C δ x :=
  C.map_mul' γ δ x

/--
The descent condition.

A cover cocycle descends to the geometric projective group exactly when it is
independent of the chosen lift.
-/
def CoverRotorCocycle.DescendsToGeometry
    {Γcover Γgeom X R : Type*}
    [Group Γcover] [Group Γgeom] [MulAction Γgeom X] [Group R]
    (C : CoverRotorCocycle Γcover Γgeom X R) : Prop :=
  ∀ ⦃γ δ : Γcover⦄,
    C.projection γ = C.projection δ →
      ∀ x : X, C γ x = C δ x

/--
Kernel anomaly.

A geometrically invisible lift may still act nontrivially on the rotor carrier.
That value is the spin/multiplier obstruction.
-/
def CoverRotorCocycle.kernelAnomaly
    {Γcover Γgeom X R : Type*}
    [Group Γcover] [Group Γgeom] [MulAction Γgeom X] [Group R]
    (C : CoverRotorCocycle Γcover Γgeom X R)
    (κ : C.projection.ker)
    (x : X) : R :=
  C (κ : Γcover) x

/--
On any subgroup whose projected action fixes `x`, the cover cocycle collapses
to a genuine homomorphism.
-/
def CoverRotorCocycle.extractFixedSubgroupHom
    {Γcover Γgeom X R : Type*}
    [Group Γcover] [Group Γgeom] [MulAction Γgeom X] [Group R]
    (C : CoverRotorCocycle Γcover Γgeom X R)
    (x : X)
    (H : Subgroup Γcover)
    (hH : ∀ γ ∈ H, C.projection γ • x = x) :
    H →* R where
  toFun γ := C (γ : Γcover) x
  map_one' := by
    exact C.map_one' x
  map_mul' γ δ := by
    have hδ : C.projection (δ : Γcover) • x = x :=
      hH (δ : Γcover) δ.property
    rw [Subgroup.coe_mul, C.map_mul' (γ : Γcover) (δ : Γcover) x, hδ]

/--
The real modular projective rotor cocycle.

The base action is an assumed real projective action of `PSL2R` on
`RealUpperHalfPlane`. The cocycle itself lives on the `SL2R` cover.
-/
abbrev RealModularProjectiveRotorCocycle
    (R : Type*) [Group R]
    [MulAction SL2R RealUpperHalfPlane] :=
  CoverRotorCocycle SL2R SL2R RealUpperHalfPlane R

/--
Cusp anomaly as a real filter limit.

No `i∞`, no complex coordinate, no complex unit. The cusp is the regime
`Y → ∞` in the positive real height coordinate.
-/
def cuspLimit_tendsto
    {R : Type*} [Group R] [TopologicalSpace R]
    [MulAction SL2R RealUpperHalfPlane]
    (C : RealModularProjectiveRotorCocycle R)
    (T : SL2R)
    (anomalyRotor : R) : Prop :=
  Tendsto
    (fun Y : PosReal => C T (verticalRay Y))
    atTop
    (𝓝 anomalyRotor)

end InfoGeometry.ProjectiveFoundation
