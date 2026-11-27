/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Optics.OperatorDerivationForms
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra

/-!
# Linearization of finite families of operator-valued one-forms

`NOperatorForm` is a finite family of pointwise functions. This construction
requires proved pointwise additivity and scalar compatibility before
producing linear one-forms.
-/

namespace InfoGeometry.Optics.OperatorDerivationForms

open InfoGeometry.OperatorAlgebra.ExteriorAlgebra

variable {R Point Tangent Value : Type*} {n : ℕ}
variable [CommRing R] [AddCommGroup Tangent] [Module R Tangent]
variable [Ring Value] [Algebra R Value]

/-- Linearize each pointwise tangent function in a finite operator-form
family, given its additivity and scalar-homogeneity laws. -/
def NOperatorForm.toOp1Form
    (ω : NOperatorForm n (Point := Point) (Tangent := Tangent) (Value := Value))
    (hadd : ∀ i p x y, ω i p (x + y) = ω i p x + ω i p y)
    (hsmul : ∀ i p (r : R) x, ω i p (r • x) = r • ω i p x) :
    Fin n → Point → Op1Form R Tangent Value :=
  fun i p =>
    { toFun := fun x => ω i p x
      map_add' := hadd i p
      map_smul' := hsmul i p }

@[simp] theorem NOperatorForm.toOp1Form_apply
    (ω : NOperatorForm n (Point := Point) (Tangent := Tangent) (Value := Value))
    (hadd : ∀ i p x y, ω i p (x + y) = ω i p x + ω i p y)
    (hsmul : ∀ i p (r : R) x, ω i p (r • x) = r • ω i p x)
    (i : Fin n) (p : Point) (x : Tangent) :
    NOperatorForm.toOp1Form ω hadd hsmul i p x = ω i p x :=
  rfl

end InfoGeometry.Optics.OperatorDerivationForms
