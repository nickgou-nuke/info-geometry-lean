import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite twisted de Rham core for Feynman-style exact relations

This owner formalizes only the algebraic core needed before a genuine
configuration-space/de Rham comparison: a chosen square-zero twist in an
exterior algebra and the differential given by left multiplication.  An IBP
relation is represented only when an explicit primitive is supplied.  No
Symanzik, graph-hypersurface, master-integral, or analytic period theorem is
claimed here.
-/

namespace InfoGeometry.Feynman.FeynmanTwistedDeRhamComplex

noncomputable section

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

abbrev Forms (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] := ExteriorAlgebra R M

/-- A twist together with the square-zero property needed for `d_ω² = 0`. -/
structure TwistedOneForm (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] where
  carrier : Forms R M
  square_zero : carrier * carrier = 0

/-- The twisted differential `d_ω(η) = ω ∧ η`, represented by left product. -/
def twistedDifferential (ω : TwistedOneForm R M) :
    Forms R M →ₗ[R] Forms R M where
  toFun η := ω.carrier * η
  map_add' η ξ := by simp [mul_add]
  map_smul' r η := by
    rw [Algebra.smul_def, Algebra.smul_def]
    rw [← mul_assoc, ← Algebra.commutes, mul_assoc]
    rfl

@[simp] theorem twistedDifferential_apply
    (ω : TwistedOneForm R M) (η : Forms R M) :
    twistedDifferential ω η = ω.carrier * η := rfl

theorem twistedDifferential_square_zero
    (ω : TwistedOneForm R M) :
    (twistedDifferential ω).comp (twistedDifferential ω) = 0 := by
  apply LinearMap.ext
  intro η
  change ω.carrier * (ω.carrier * η) = 0
  rw [← mul_assoc, ω.square_zero, zero_mul]

/-- The explicit twisted-exact representative of an IBP relation. -/
def ibpRelation
    (ω : TwistedOneForm R M) (primitive : Forms R M) : Forms R M :=
  twistedDifferential ω primitive

theorem ibp_relation_is_twisted_exact
    (ω : TwistedOneForm R M) (primitive : Forms R M) :
    ibpRelation ω primitive = twistedDifferential ω primitive := rfl

theorem twisted_exact_relation_is_closed
    (ω : TwistedOneForm R M) (primitive : Forms R M) :
    twistedDifferential ω (ibpRelation ω primitive) = 0 := by
  rw [ibpRelation]
  simpa [LinearMap.comp_apply] using
    congrArg (fun f : Forms R M →ₗ[R] Forms R M => f primitive)
      (twistedDifferential_square_zero ω)

end
end InfoGeometry.Feynman.FeynmanTwistedDeRhamComplex
