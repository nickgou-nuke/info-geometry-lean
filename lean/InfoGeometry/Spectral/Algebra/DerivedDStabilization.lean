import InfoGeometry.Spectral.Algebra.GenericDerivedCouple
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Stabilization of the derived `D` term

The derived `D` term of an exact couple is the image of the incoming `i` map.
When that map is surjective, this image is the whole target module.  This file
records the resulting linear equivalence directly, rather than packaging
surjectivity into a boundedness or convergence record.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}
variable {D E : I → Type u}
variable [∀ p, AddCommGroup (D p)] [∀ p, AddCommGroup (E p)]
variable [∀ p, Module R (D p)] [∀ p, Module R (E p)]
variable {iDeg jDeg kDeg : I ≃ I}

/-- A surjective incoming `i` map identifies the derived `D` term with the
whole target `D` module. -/
noncomputable def directDerivedDEquivOfIncomingISurjective
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I)
    (h : Function.Surjective (C.incomingI p)) :
    C.DirectDerivedD p ≃ₗ[R] D p :=
  (LinearEquiv.ofEq
      (LinearMap.range (C.incomingI p))
      ⊤
      (LinearMap.range_eq_top.mpr h)).trans
    Submodule.topEquiv

@[simp]
theorem directDerivedDEquivOfIncomingISurjective_apply
    (C : GradedExactCouple R I D E iDeg jDeg kDeg) (p : I)
    (h : Function.Surjective (C.incomingI p))
    (x : C.DirectDerivedD p) :
    C.directDerivedDEquivOfIncomingISurjective p h x = x.1 :=
  rfl

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
