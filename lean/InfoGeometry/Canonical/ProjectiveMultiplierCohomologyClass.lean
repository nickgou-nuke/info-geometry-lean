import InfoGeometry.Canonical.ProjectiveMultiplierCocycle
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Rephasing classes of projective multipliers

The repository has native multiplier/cocycle laws, but it does not contain a
group-cohomology computation for the Klein/Pin layer.  This file therefore
defines the honest algebraic classification available without analytic
assumptions: normalized multiplicative two-cocycles modulo pointwise
rephasing.  The quotient is the formal cohomology-class carrier; identifying
it with a named `H²` group is a separate theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.ProjectiveMultiplierCohomologyClass

universe uG uC

variable (G : Type uG) (C : Type uC) [Group G] [CommGroup C]

structure TwoCocycle where
  toFun : G → G → C
  one_left : ∀ g, toFun 1 g = 1
  one_right : ∀ g, toFun g 1 = 1
  cocycle : ∀ g h k,
    toFun g h * toFun (g * h) k =
      toFun h k * toFun g (h * k)

instance : CoeFun (TwoCocycle G C) (fun _ => G → G → C) :=
  ⟨TwoCocycle.toFun⟩

namespace TwoCocycle

variable {G C}

@[simp] theorem one_left_apply (c : TwoCocycle G C) (g : G) : c 1 g = 1 :=
  c.one_left g

@[simp] theorem one_right_apply (c : TwoCocycle G C) (g : G) : c g 1 = 1 :=
  c.one_right g

end TwoCocycle

/-- One elementary change of scalar lift/trivialization. -/
def ElementaryRephase (c d : TwoCocycle G C) : Prop :=
  ∃ f : G → C, ∀ g h,
    d g h = f g * f h * (f (g * h))⁻¹ * c g h

/-! `EqvGen` supplies the reflexive/symmetric/transitive closure of elementary
rephasings, so no unproved cancellation or cochain-complex theorem is hidden
in the quotient. -/
abbrev Rephased (c d : TwoCocycle G C) : Prop :=
  Relation.EqvGen (ElementaryRephase G C) c d

instance rephasedSetoid : Setoid (TwoCocycle G C) :=
  Relation.EqvGen.setoid (ElementaryRephase G C)

/-!
The quotient is the precise algebraic “cohomology class” object available in
this repository.  No claim is made here that it is canonically isomorphic to
group cohomology without an additional cochain-complex development.
-/
def Class := Quotient (rephasedSetoid G C)

def classOf (c : TwoCocycle G C) : Class G C := Quotient.mk' c

theorem classOf_eq_iff {c d : TwoCocycle G C} :
    classOf G C c = classOf G C d ↔ Rephased G C c d := by
  exact Quotient.eq_iff_equiv

end InfoGeometry.Canonical.ProjectiveMultiplierCohomologyClass
