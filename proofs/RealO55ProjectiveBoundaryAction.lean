import proofs.RealO55CartanDieudonne
import InfoGeometry.Projective.Cl55NullBoundaryBridge

/-!
# Full real Pin action on the `Q55` projective null boundary

This bridge uses the existing full-real `Pin(5,5)` vector representation and
the existing generic projective-null quotient.  It does not identify the full
real Pin carrier with the older star-unitary `Clifford55.Pin55` carrier.
-/

noncomputable section

namespace RealO55ProjectiveBoundaryAction

open Clifford55
open RealPin55Core
open RealPin55TwistedAction
open RealPin55OrthogonalAction
open RealPin55QuadraticRepresentation
open InfoGeometry.Projective
open InfoGeometry.Projective.Cl55NullBoundaryBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryDatum

abbrev Boundary := Cl55NullBoundaryBridge.Boundary
abbrev NullRep := Cl55NullBoundaryBridge.NullRep

/-- The full-real Pin action as an equivariant map of `Q55` carriers. -/
noncomputable def fullPinBoundaryHom (g : FullPin55) :
    BoundaryHom Cl55NullBoundaryBridge.datum Cl55NullBoundaryBridge.datum where
  toFun := fullPinVectorRepresentation g
  map_zero := (fullPinVectorRepresentation g).map_zero
  map_null := by
    intro v hv
    calc
      Q55 (fullPinVectorRepresentation g v) =
          Q55 (twistedVector g v) := by rfl
      _ = Q55 v := fullPin55_preserves_Q g v
      _ = 0 := hv
  map_ne_zero := by
    intro v hv hzero
    apply hv
    apply (fullPinVectorRepresentation g).injective
    have hzero0 : fullPinVectorRepresentation g v = (0 : V55) := by
      simpa [Cl55NullBoundaryBridge.datum] using hzero
    calc
      fullPinVectorRepresentation g v = 0 := hzero0
      _ = fullPinVectorRepresentation g (0 : V55) := by
        rw [(fullPinVectorRepresentation g).map_zero]
      _ = fullPinVectorRepresentation g Cl55NullBoundaryBridge.datum.zero := rfl
  map_scale := by
    intro u v
    exact (fullPinVectorRepresentation g).map_smul (u : ℝ) v

@[simp]
theorem fullPinBoundaryHom_apply (g : FullPin55) (v : V55) :
    (fullPinBoundaryHom g).toFun v = fullPinVectorRepresentation g v :=
  rfl

/-- Descent of the full-real Pin action to the projective null quotient. -/
noncomputable def fullPinBoundaryAction (g : FullPin55) : Boundary → Boundary :=
  BoundaryHom.mapBoundary (fullPinBoundaryHom g)

@[simp]
theorem fullPinBoundaryAction_mk (g : FullPin55) (Z : NullRep) :
    fullPinBoundaryAction g (Cl55NullBoundaryBridge.mk Z) =
      nullMk Cl55NullBoundaryBridge.datum
        (BoundaryHom.mapNullRep (fullPinBoundaryHom g) Z) :=
  rfl

theorem fullPinBoundaryAction_one (Z : NullRep) :
    fullPinBoundaryAction (1 : FullPin55) (Cl55NullBoundaryBridge.mk Z) =
      Cl55NullBoundaryBridge.mk Z := by
  rw [fullPinBoundaryAction_mk]
  apply congrArg (nullMk Cl55NullBoundaryBridge.datum)
  apply NullRep.ext_Z
  change fullPinVectorRepresentation (1 : FullPin55) Z.Z = Z.Z
  rw [map_one]
  rfl

theorem fullPinBoundaryAction_mul (g h : FullPin55) (Z : NullRep) :
    fullPinBoundaryAction (g * h) (Cl55NullBoundaryBridge.mk Z) =
      fullPinBoundaryAction g
        (fullPinBoundaryAction h (Cl55NullBoundaryBridge.mk Z)) := by
  rw [fullPinBoundaryAction_mk, fullPinBoundaryAction_mk]
  apply congrArg (nullMk Cl55NullBoundaryBridge.datum)
  apply NullRep.ext_Z
  change fullPinVectorRepresentation (g * h) Z.Z =
    fullPinVectorRepresentation g (fullPinVectorRepresentation h Z.Z)
  rw [map_mul]
  rfl

/-- The full-real Pin action on the projective null boundary is a monoid
homomorphism, hence a genuine noncommutative group action. -/
noncomputable def fullPinBoundaryRepresentation :
    FullPin55 →* Function.End Boundary where
  toFun := fullPinBoundaryAction
  map_one' := by
    funext x
    refine Quotient.inductionOn
      (s := nullRepSetoid Cl55NullBoundaryBridge.datum) x ?_
    intro Z
    exact fullPinBoundaryAction_one Z
  map_mul' := by
    intro g h
    funext x
    refine Quotient.inductionOn
      (s := nullRepSetoid Cl55NullBoundaryBridge.datum) x ?_
    intro Z
    change fullPinBoundaryAction (g * h)
        (Cl55NullBoundaryBridge.mk Z) =
      fullPinBoundaryAction g
        (fullPinBoundaryAction h (Cl55NullBoundaryBridge.mk Z))
    exact fullPinBoundaryAction_mul g h Z

end RealO55ProjectiveBoundaryAction

end noncomputable section
