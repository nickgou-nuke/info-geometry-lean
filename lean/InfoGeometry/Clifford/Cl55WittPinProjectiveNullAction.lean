import InfoGeometry.Clifford.Cl55WittPinOrthogonalAction
import InfoGeometry.Canonical.Cl55ProjectiveBoundary
import InfoGeometry.Canonical.ProjectiveFoundation

namespace InfoGeometry.Clifford.Clifford55

/-!
# Projective null-cone action of the native `Pin(5,5)` carrier

This file transports the already-proved ordinary-conjugation action of native
`Pin55` to projective `V55`.  It is distinct from the `realSplitPin55`
quotient owner: no second Pin carrier, quadratic form, or projective quotient
is introduced here.
-/

noncomputable section

open InfoGeometry.Canonical.ProjectiveFoundation
open InfoGeometry.Canonical.Cl55ProjectiveBoundary
open scoped LinearAlgebra.Projectivization

noncomputable def pinV55LinearAction :
    Pin55 →* (V55 ≃ₗ[ℝ] V55) where
  toFun := pinConjActionEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change pinConjAction (1 : Pin55) v = v
    rw [pinConjAction_one]
    rfl
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro v
    change pinConjAction (g * h) v =
      pinConjAction g (pinConjAction h v)
    rw [pinConjAction_mul]
    rfl

noncomputable def pinProjectiveRepresentation :
    ProjectiveRepresentation ℝ Pin55 V55 :=
  ProjectiveRepresentation.ofLinearHom pinV55LinearAction

@[simp] theorem pinProjectiveRepresentation_multiplier
    (g h : Pin55) :
    pinProjectiveRepresentation.multiplier g h = 1 :=
  rfl

noncomputable def pinProjectivizationAction :
    Pin55 →* Function.End (ℙ ℝ V55) :=
  pinProjectiveRepresentation.projectivizationAction

theorem pinProjectivizationAction_map_mul
    (g h : Pin55) :
    pinProjectivizationAction (g * h) =
      pinProjectivizationAction g ∘ pinProjectivizationAction h := by
  exact pinProjectiveRepresentation.projectivizationMap_mul g h

theorem pinProjectivization_preserves_null
    (g : Pin55) (p : ℙ ℝ V55)
    (hp : IsProjectiveNull Q55 p) :
    IsProjectiveNull Q55
      (pinProjectiveRepresentation.projectivizationMap g p) := by
  induction p using Projectivization.ind with
  | h v hv =>
      change Q55 v = 0 at hp
      rw [ProjectiveRepresentation.projectivizationMap_mk]
      change Q55 (pinConjActionEquiv g v) = 0
      change Q55 (pinConjAction g v) = 0
      rw [pinConjAction_preserves_Q55, hp]

end

end InfoGeometry.Clifford.Clifford55
