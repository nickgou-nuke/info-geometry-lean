import InfoGeometry.Canonical.CanonicalZornTrialitySpinEquivariance

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornCoordinateOuterTrialityNaturality

open CanonicalZornCompositionTriality
open CanonicalZornTrialitySpinEquivariance

abbrev Coordinates := Fin 8 → ℂ

def cyclic : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

def signedPermVec (p : Equiv.Perm (Fin 3)) (x : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => (Equiv.Perm.sign p : ℂ) * x (p i)

theorem signedPermVec_comp (p q : Equiv.Perm (Fin 3)) (x : Fin 3 → ℂ) :
    signedPermVec p (signedPermVec q x) = signedPermVec (q * p) x := by
  funext i
  simp [signedPermVec, Equiv.Perm.sign_mul, mul_assoc]
  ring

def signedCoordinateAction (p : Equiv.Perm (Fin 3)) : Coordinates → Coordinates :=
  fun v =>
    ![v 0,
      signedPermVec p (![v 1, v 2, v 3]) 0,
      signedPermVec p (![v 1, v 2, v 3]) 1,
      signedPermVec p (![v 1, v 2, v 3]) 2,
      signedPermVec p (![v 4, v 5, v 6]) 0,
      signedPermVec p (![v 4, v 5, v 6]) 1,
      signedPermVec p (![v 4, v 5, v 6]) 2,
      v 7]

def typedSignedCoordinateAction (p : Equiv.Perm (Fin 3))
    (sector : TrialitySector) : ZornCopy sector → ZornCopy sector :=
  fun X =>
    (copyLinearEquivCoordinates sector).symm
      (signedCoordinateAction p ((copyLinearEquivCoordinates sector) X))

def typedCoordinateTransport (a b : TrialitySector) :
    ZornCopy a → ZornCopy b :=
  fun X =>
    (copyLinearEquivCoordinates b).symm ((copyLinearEquivCoordinates a) X)

theorem typedSignedCoordinateAction_coordinates
    (p : Equiv.Perm (Fin 3)) (sector : TrialitySector)
    (X : ZornCopy sector) :
    (copyLinearEquivCoordinates sector)
        (typedSignedCoordinateAction p sector X) =
      signedCoordinateAction p ((copyLinearEquivCoordinates sector) X) := by
  simp [typedSignedCoordinateAction]

theorem typedSignedCoordinateAction_natural
    (p : Equiv.Perm (Fin 3)) (a b : TrialitySector) (X : ZornCopy a) :
    typedCoordinateTransport a b
        (typedSignedCoordinateAction p a X) =
      typedSignedCoordinateAction p b
        (typedCoordinateTransport a b X) := by
  apply ZornCopy.ext
  apply zornCoordinates_injective
  simp [typedCoordinateTransport, typedSignedCoordinateAction,
    signedCoordinateAction]

theorem signedCoordinateAction_cyclic
    (v : Coordinates) :
    signedCoordinateAction cyclic v =
      CanonicalZornCompositionTriality.zornCoordinates
        (CanonicalZornProjectiveTKKBridge.canonicalTriality
          (CanonicalZornCompositionTriality.coordinatesToZorn v)) := by
  funext i
  fin_cases i <;>
    simp [signedCoordinateAction, signedPermVec, cyclic,
      CanonicalZornCompositionTriality.zornCoordinates,
      CanonicalZornCompositionTriality.coordinatesToZorn,
      CanonicalZornProjectiveTKKBridge.canonicalTriality,
      Equiv.swap_apply_def,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

theorem typedSignedCoordinateAction_cyclic_eq_axisCycleCopy
    (sector : TrialitySector) (X : ZornCopy sector) :
    typedSignedCoordinateAction cyclic sector X = axisCycleCopy sector X := by
  apply ZornCopy.ext
  apply zornCoordinates_injective
  change signedCoordinateAction cyclic
      ((copyLinearEquivCoordinates sector) X) =
    (copyLinearEquivCoordinates sector) (axisCycleCopy sector X)
  rw [signedCoordinateAction_cyclic]
  rfl

theorem typedTransport_vectorToSpinorPlus_natural
    (p : Equiv.Perm (Fin 3)) (V : Vector8) :
    typedCoordinateTransport .vector .spinorPlus
        (typedSignedCoordinateAction p .vector V) =
      typedSignedCoordinateAction p .spinorPlus
        (typedCoordinateTransport .vector .spinorPlus V) := by
  exact typedSignedCoordinateAction_natural p .vector .spinorPlus V

theorem typedTransport_spinorPlusToSpinorMinus_natural
    (p : Equiv.Perm (Fin 3)) (S : SpinorPlus8) :
    typedCoordinateTransport .spinorPlus .spinorMinus
        (typedSignedCoordinateAction p .spinorPlus S) =
      typedSignedCoordinateAction p .spinorMinus
        (typedCoordinateTransport .spinorPlus .spinorMinus S) := by
  exact typedSignedCoordinateAction_natural p .spinorPlus .spinorMinus S

theorem typedTransport_spinorMinusToVector_natural
    (p : Equiv.Perm (Fin 3)) (C : SpinorMinus8) :
    typedCoordinateTransport .spinorMinus .vector
        (typedSignedCoordinateAction p .spinorMinus C) =
      typedSignedCoordinateAction p .vector
        (typedCoordinateTransport .spinorMinus .vector C) := by
  exact typedSignedCoordinateAction_natural p .spinorMinus .vector C

end InfoGeometry.Canonical.CanonicalZornCoordinateOuterTrialityNaturality
