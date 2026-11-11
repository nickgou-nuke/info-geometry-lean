/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.ExteriorKleinDeterminantCovariance

/-!
# Constructed incidence transport for invertible four-vector actions

The existing conditional incidence-fiber theorem is applied with a constructed
equivalence and proved determinant covariance. Fibers here are full polar
kernels; this file does not add an action on projective rays.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorKleinOperatorAction

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Projective.ExteriorKleinNullTwistor
open InfoGeometry.Projective.ExteriorKleinNullTwistorIncidence

/-- Coordinate identification with the existing incidence owner's carrier. -/
def pluckerCoordinateEquiv : Bivector4 ≃ InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ where
  toFun P := ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
  invFun P := ⟨P.p01, P.p02, P.p03, P.p12, P.p13, P.p23⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

open InfoGeometry.Projective.KleinQuadricIncidence.Plucker6

theorem incidenceForm_coordinates (P Q : Bivector4) :
    incidenceForm (pluckerCoordinateEquiv P) (pluckerCoordinateEquiv Q) =
      QuadraticMap.polar exteriorKleinQuadraticForm
        (exteriorBivectorLinearEquiv.symm P) (exteriorBivectorLinearEquiv.symm Q) := by
  rw [exteriorKleinQuadraticForm_polar]
  simp only [LinearEquiv.apply_symm_apply, pluckerCoordinateEquiv, Equiv.coe_fn_mk,
    incidenceForm]
  ring

theorem incidenceForm_bivectorAction (A : Module.End ℝ Vec4) (P Q : Bivector4) :
    incidenceForm (pluckerCoordinateEquiv (bivectorAction A P))
        (pluckerCoordinateEquiv (bivectorAction A Q)) =
      LinearMap.det A * incidenceForm (pluckerCoordinateEquiv P) (pluckerCoordinateEquiv Q) := by
  rw [incidenceForm_coordinates, incidenceForm_coordinates]
  simpa [bivectorAction] using exteriorKleinPolar_map A
    (exteriorBivectorLinearEquiv.symm P) (exteriorBivectorLinearEquiv.symm Q)

/-- The incidence-coordinate equivalence induced by an actual four-vector inverse. -/
def pluckerEquiv (A : Vec4 ≃ₗ[ℝ] Vec4) :
    InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ ≃
      InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ :=
  pluckerCoordinateEquiv.symm.trans ((bivectorEquiv A).toEquiv.trans pluckerCoordinateEquiv)

theorem incidenceForm_pluckerEquiv (A : Vec4 ≃ₗ[ℝ] Vec4)
    (P Q : InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ) :
    incidenceForm (pluckerEquiv A P) (pluckerEquiv A Q) =
      LinearMap.det A.toLinearMap * incidenceForm P Q := by
  change incidenceForm
      (pluckerCoordinateEquiv (bivectorAction A.toLinearMap (pluckerCoordinateEquiv.symm P)))
      (pluckerCoordinateEquiv (bivectorAction A.toLinearMap (pluckerCoordinateEquiv.symm Q))) = _
  rw [incidenceForm_bivectorAction]
  simp only [Equiv.apply_symm_apply]

/-- Every input of the existing transport theorem is constructed or proved. -/
theorem incidenceFiber_pluckerEquiv_image (A : Vec4 ≃ₗ[ℝ] Vec4)
    (Y : InfoGeometry.Projective.KleinQuadric.Plucker6 ℝ) :
    incidenceFiber (pluckerEquiv A Y) = pluckerEquiv A '' incidenceFiber Y := by
  exact incidenceFiber_erlangen_image (pluckerEquiv A) (LinearMap.det A.toLinearMap)
    A.isUnit_det'.ne_zero (incidenceForm_pluckerEquiv A) Y

end InfoGeometry.Projective.ExteriorKleinOperatorAction
