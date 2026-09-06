import InfoGeometry.Spectral.Homotopy.CategoricalCofiber

/-!
# Mapping-cone compatibility layer

The historical HoTT port uses a higher-inductive mapping cone.  Lean 4's
ordinary categorical replacement is the pushout of `f` with the map to
`Unit`, already owned by `CategoricalCofiber`.  This file provides the
standard mapping-cone names without claiming a topological realization.
-/

namespace InfoGeometry.Spectral.Homotopy.MappingCone

noncomputable section

open InfoGeometry.Spectral.Homotopy.CategoricalCofiber

variable {α β γ : Type}

abbrev mappingCone (f : α → β) : Type := carrier f

abbrev quotient (f : α → β) : β → mappingCone f :=
  CategoricalCofiber.quotient f

abbrev apex (f : α → β) : Unit → mappingCone f :=
  CategoricalCofiber.basepoint f

theorem glue (f : α → β) (x : α) :
    quotient f (f x) = apex f () :=
  CategoricalCofiber.quotient_glue f x

abbrev lift (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ()) : mappingCone f → γ :=
  CategoricalCofiber.lift f u v h

@[simp]
theorem lift_quotient (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ()) (y : β) :
    lift f u v h (quotient f y) = u y :=
  CategoricalCofiber.lift_quotient f u v h y

@[simp]
theorem lift_apex (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ()) :
    lift f u v h (apex f ()) = v () :=
  CategoricalCofiber.lift_basepoint f u v h

theorem lift_unique (f : α → β) (u : β → γ) (v : Unit → γ)
    (h : ∀ x, u (f x) = v ()) (k : mappingCone f → γ)
    (hk : ∀ y, k (quotient f y) = u y)
    (hk' : k (apex f ()) = v ()) :
    k = lift f u v h :=
  CategoricalCofiber.lift_unique f u v h k hk hk'

end

end InfoGeometry.Spectral.Homotopy.MappingCone
