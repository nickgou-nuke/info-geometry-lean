/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import InfoGeometry.Meta.Architecture

/-!
# Two-operator Onsager forms

The response-form carrier is independent of a material susceptibility model.
These declarations retain their original namespace and definitions from
`SusceptibilityOnsagerStress`, which imports this owner.
-/

namespace InfoGeometry.Thermo.SusceptibilityOnsagerStress

/-- A scalar bilinear response kernel on operator perturbations. -/
abbrev TwoOperatorForm
    (Op : Type*)
    [AddCommMonoid Op] [Module ℝ Op] : Type _ :=
  LinearMap.BilinForm ℝ Op

/-- A reciprocal nonnegative response form. Concrete models must prove both laws. -/
structure OnsagerTwoOperatorForm
    (Op : Type*)
    [AddCommMonoid Op] [Module ℝ Op] where
  /-- Scalar response coefficient for a pair of operator perturbations. -/
  form : TwoOperatorForm Op
  /-- Onsager reciprocity. -/
  symmetric : ∀ A B : Op, form A B = form B A
  /-- Nonnegativity of the quadratic response. -/
  diagonal_nonnegative : ∀ A : Op, 0 ≤ form A A

namespace OnsagerTwoOperatorForm

variable
    {Op : Type*}
    [AddCommMonoid Op] [Module ℝ Op]

variable (L : OnsagerTwoOperatorForm Op)

/-- Re-export of Onsager reciprocity. -/
theorem swap
    (A B : Op) :
    L.form A B = L.form B A :=
  L.symmetric A B

/-- The Onsager quadratic response is nonnegative. -/
theorem apply_self_nonnegative
    (A : Op) :
    0 ≤ L.form A A :=
  L.diagonal_nonnegative A

attribute [rep_depth thermo] OnsagerTwoOperatorForm.swap
  OnsagerTwoOperatorForm.apply_self_nonnegative

end OnsagerTwoOperatorForm

end InfoGeometry.Thermo.SusceptibilityOnsagerStress
