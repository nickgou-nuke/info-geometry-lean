import InfoGeometry.Physics.B3PresentedGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.YangBaxterQSwap
import InfoGeometry.Canonical.BoundarySpinFiveGradeBridge
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Presented braid representation for the boundary/anyon lane

The native Jones--Temperley--Lieb matrices already satisfy the defining
`B₃` Artin relation.  This owner exposes the resulting genuine group
homomorphism and records its generator packet alongside the typed Majorana
boundary readout.  No claim of an intertwiner between the two carriers is made
here; that is a separate equivariance theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.BoundaryBraidRepresentation

open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Physics.YangBaxterQSwap

abbrev BoundaryBraidGroup := B3
abbrev BoundaryBraidCarrier := GL8
abbrev BoundaryBraidState := InfoGeometry.Algebra.FiniteSpin.Vec8C
abbrev BoundaryBraidLinearCarrier :=
  LinearMap.GeneralLinearGroup ℂ BoundaryBraidState

def boundaryBraidRepresentation : BoundaryBraidGroup →* BoundaryBraidCarrier :=
  phi

/-- Native matrix-to-linear transport of invertible `8 × 8` matrices. -/
def matrixUnitToLinearUnit : BoundaryBraidCarrier →* BoundaryBraidLinearCarrier :=
  Units.map
    (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin 8)).toRingEquiv.toMonoidHom

/-- The Jones--Temperley--Lieb boundary braid representation on the native
eight-dimensional complex module rather than its matrix-coordinate carrier. -/
def boundaryBraidLinearRepresentation :
    BoundaryBraidGroup →* BoundaryBraidLinearCarrier :=
  matrixUnitToLinearUnit.comp boundaryBraidRepresentation

@[simp] theorem boundaryBraidLinearRepresentation_first_generator :
    boundaryBraidLinearRepresentation
        (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) =
      matrixUnitToLinearUnit s0_unit := by
  rw [boundaryBraidLinearRepresentation, MonoidHom.comp_apply,
    boundaryBraidRepresentation, phi_sig0]

@[simp] theorem boundaryBraidLinearRepresentation_second_generator :
    boundaryBraidLinearRepresentation
        (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) =
      matrixUnitToLinearUnit s1_unit := by
  rw [boundaryBraidLinearRepresentation, MonoidHom.comp_apply,
    boundaryBraidRepresentation, phi_sig1]

theorem boundaryBraidRepresentation_first_generator :
    boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) =
      s0_unit := by
  exact phi_sig0

theorem boundaryBraidRepresentation_second_generator :
    boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) =
      s1_unit := by
  exact phi_sig1

theorem boundaryBraidRepresentation_artin :
    boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) *
          boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) *
          boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) =
      boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) *
      boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) *
          boundaryBraidRepresentation (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) := by
  rw [boundaryBraidRepresentation_first_generator,
    boundaryBraidRepresentation_second_generator]
  exact units_artin_relation

theorem boundaryBraidRepresentation_map_mul (g h : BoundaryBraidGroup) :
    boundaryBraidRepresentation (g * h) =
      boundaryBraidRepresentation g * boundaryBraidRepresentation h := by
  exact map_mul boundaryBraidRepresentation g h

theorem boundaryYangBaxter_relation (q : ℂ) :
    C12 q * C23 q * C12 q = C23 q * C12 q * C23 q :=
  yang_baxter_relation q

end InfoGeometry.Canonical.BoundaryBraidRepresentation
