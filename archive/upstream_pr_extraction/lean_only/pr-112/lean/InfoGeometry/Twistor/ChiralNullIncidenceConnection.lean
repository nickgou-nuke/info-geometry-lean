import InfoGeometry.Twistor.TwoTwistorSpacetimeNode

/-!
# Discrete transport on a null-incidence network

This owner is deliberately finite and algebraic.  It supplies a genuine
transport carrier on a chosen incidence network and defines triangle
holonomy.  It does not identify that holonomy with a smooth curvature tensor.
-/

namespace InfoGeometry.Twistor.ChiralNullIncidenceConnection

open InfoGeometry.Twistor.PenroseIncidence

variable {R : Type*} [CommRing R]
variable {F : Type*} [AddCommGroup F] [Module R F]
variable {N : Type*}

/-- A finite linear transport system over a set of incidence nodes. -/
structure DiscreteLinearConnection (R : Type*) [CommRing R]
    (F : Type*) [AddCommGroup F] [Module R F] (N : Type*) where
  transport : N → N → F ≃ₗ[R] F

namespace DiscreteLinearConnection

variable (C : DiscreteLinearConnection R F N)

/-- Transport around the ordered triangle `a → b → c → a`. -/
def triangleHolonomy (a b c : N) : F ≃ₗ[R] F :=
  (C.transport a b).trans ((C.transport b c).trans (C.transport c a))

/-- Flatness of one discrete incidence triangle. -/
def TriangleFlat (a b c : N) : Prop :=
  C.triangleHolonomy a b c = LinearEquiv.refl R F

theorem triangleHolonomy_apply_of_flat
    (a b c : N) (hflat : C.TriangleFlat a b c) (v : F) :
    C.triangleHolonomy a b c v = v := by
  rw [hflat]
  rfl

theorem triangleFlat_of_holonomy_apply
    (a b c : N)
    (happly : ∀ v : F, C.triangleHolonomy a b c v = v) :
    C.TriangleFlat a b c := by
  ext v
  exact happly v

end DiscreteLinearConnection

end InfoGeometry.Twistor.ChiralNullIncidenceConnection
