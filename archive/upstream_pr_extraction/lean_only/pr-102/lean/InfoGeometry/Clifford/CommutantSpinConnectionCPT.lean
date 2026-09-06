import InfoGeometry.Physics.AlgebraicTomitaTakesakiBridge
import InfoGeometry.Physics.TomitaTakesakiModularFlow
import InfoGeometry.Optics.OperatorValuedConnection
import InfoGeometry.Optics.OperatorDerivationForms
import InfoGeometry.Canonical.KleinMonodromyRepresentationSpace

/-!
# Commutant-side spin connection and CPT/Klein readout

This owner composes existing theorem-backed infrastructure.  The commutant is
the existing `Physics.Commutant`, Tomita transport is the existing
`AntiAutomorphism`/`IsTomitaConjugation` API, curvature is the existing
`OperatorValuedConnection.curvature`, and the Klein presentation is imported
from `KleinMonodromyRepresentationSpace`.

The only new result is their algebraic compatibility: an orientation-reversing
anti-automorphism transports a connection with the compensating sign on its
derivative, and therefore negates curvature.
-/

noncomputable section

namespace InfoGeometry.Clifford.CommutantSpinConnectionCPT

open InfoGeometry.Physics
open InfoGeometry.Physics.AlgebraicTomitaTakesaki
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Canonical.KleinMonodromyRepresentationSpace

variable {A Point Tangent : Type*} [Ring A]

theorem anti_map_zero (J : AntiAutomorphism A) :
    J.toFun 0 = 0 := by
  have h := J.map_add 0 0
  have h' : J.toFun 0 + 0 = J.toFun 0 + J.toFun 0 := by
    simpa using h
  exact (add_left_cancel h').symm

theorem anti_map_neg (J : AntiAutomorphism A) (x : A) :
    J.toFun (-x) = -J.toFun x := by
  have h := J.map_add x (-x)
  rw [show x + -x = 0 by simp, anti_map_zero J] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem anti_map_sub (J : AntiAutomorphism A) (x y : A) :
    J.toFun (x - y) = J.toFun x - J.toFun y := by
  rw [sub_eq_add_neg, J.map_add, anti_map_neg]
  simp only [sub_eq_add_neg]

def commutantConnection
    (J : AntiAutomorphism A)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A)) :
    Connection (Point := Point) (Tangent := Tangent) (Value := A) where
  form := fun p X => J.toFun (C.form p X)
  derivative := fun p X Y => -J.toFun (C.derivative p X Y)
  derivative_swap := by
    intro p X Y
    rw [C.derivative_swap, anti_map_neg]
  derivative_same := by
    intro p X
    rw [C.derivative_same, anti_map_zero]
    simp

theorem commutantConnection_curvature
    (J : AntiAutomorphism A)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (p : Point) (X Y : Tangent) :
    curvature (commutantConnection J C) p X Y =
      -J.toFun (curvature C p X Y) := by
  unfold curvature wedgeSquare commutantConnection
  change (-J.toFun (C.derivative p X Y)) +
      (J.toFun (C.form p X) * J.toFun (C.form p Y) -
        J.toFun (C.form p Y) * J.toFun (C.form p X)) =
    -J.toFun (C.derivative p X Y +
      (C.form p X * C.form p Y - C.form p Y * C.form p X))
  rw [J.map_add, anti_map_sub, J.map_mul, J.map_mul]
  noncomm_ring

/-! The existing Fréchet derivation owner transports the curvature channel by
the Leibniz rule.  Combined with the anti-connection theorem above, this is
the precise conditional bridge; the derivation/anti-automorphism compatibility
is explicit rather than inferred. -/
theorem frechetDerivation_commutantConnection_curvature
    {A Point Tangent : Type*}
    [NormedRing A] [NormedAlgebra ℝ A]
    (D : FrechetOperatorDerivation ℝ A)
    (J : AntiAutomorphism A)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := A))
    (hDJ : ∀ a : A, D (J.toFun a) = J.toFun (D a))
    (p : Point) (X Y : Tangent) :
    D (curvature (commutantConnection J C) p X Y) =
      -J.toFun (D (curvature C p X Y)) := by
  rw [commutantConnection_curvature J C p X Y]
  rw [D.toContinuousLinearMap.map_neg, hDJ]

theorem commutant_side_transport
    (J : AntiAutomorphism A) (S : Set A)
    (hJ : IsTomitaConjugation J S) (x : A) :
    x ∈ Commutant A S ↔ J.toFun x ∈ S := by
  exact tomita_conjugation_maps_commutant_to_algebra J S hJ x

theorem tomita_commutant_image_eq
    (T : TomitaConjugationData A) (S : Set A)
    (hT : TomitaCommutantData A T S) :
    tomitaImage A T S = Commutant A S := by
  exact tomita_image_eq_commutant A T S hT

end InfoGeometry.Clifford.CommutantSpinConnectionCPT
