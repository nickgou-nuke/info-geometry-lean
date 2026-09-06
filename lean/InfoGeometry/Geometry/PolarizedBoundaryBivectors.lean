import InfoGeometry.Clifford.PolarizedBoundaryInvolutions
import InfoGeometry.Canonical.HodgeStar4DFinite
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! Native exterior bivectors for the polarized boundary carrier. -/

noncomputable section

namespace InfoGeometry.Geometry.PolarizedBoundaryBivectors

open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Clifford.PolarizedMinkowski55
open InfoGeometry.Canonical.HodgeStar4DFinite

abbrev Bivector13 := ⋀[ℝ]^2 Minkowski13

def nativeWedge (u v : Minkowski13) : Bivector13 :=
  exteriorPower.ιMulti ℝ 2 ![u, v]

def wedgeCoefficients (u v : Minkowski13) : TwoFormC :=
  ![((u.1 * v.2 0 - u.2 0 * v.1 : ℝ) : ℂ),
    ((u.1 * v.2 1 - u.2 1 * v.1 : ℝ) : ℂ),
    ((u.1 * v.2 2 - u.2 2 * v.1 : ℝ) : ℂ),
    ((u.2 1 * v.2 2 - u.2 2 * v.2 1 : ℝ) : ℂ),
    ((u.2 2 * v.2 0 - u.2 0 * v.2 2 : ℝ) : ℂ),
    ((u.2 0 * v.2 1 - u.2 1 * v.2 0 : ℝ) : ℂ)]

@[simp] theorem wedgeCoefficients_self (u : Minkowski13) :
    wedgeCoefficients u u = 0 := by
  funext i
  fin_cases i <;> simp [wedgeCoefficients, mul_comm]

theorem wedgeCoefficients_swap (u v : Minkowski13) :
    wedgeCoefficients v u = -wedgeCoefficients u v := by
  funext i
  fin_cases i <;> simp [wedgeCoefficients] <;> ring

def coefficientAlternating :
    AlternatingMap ℝ Minkowski13 TwoFormC (Fin 2) where
  toFun m := wedgeCoefficients (m 0) (m 1)
  map_update_add' m i u v := by
    fin_cases i <;> funext j <;> fin_cases j <;>
      simp [wedgeCoefficients, Function.update] <;> push_cast <;> ring
  map_update_smul' m i r u := by
    fin_cases i <;> funext j <;> fin_cases j <;>
      simp [wedgeCoefficients, Function.update] <;> push_cast <;> ring
  map_eq_zero_of_eq' m i j hij hne := by
    have h01 : m 0 = m 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    simpa only [h01] using wedgeCoefficients_self (m 1)

def bivectorReadout : Bivector13 →ₗ[ℝ] TwoFormC :=
  exteriorPower.alternatingMapLinearEquiv coefficientAlternating

@[simp] theorem bivectorReadout_wedge (u v : Minkowski13) :
    bivectorReadout (nativeWedge u v) = wedgeCoefficients u v := by
  rw [bivectorReadout, nativeWedge,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem nativeWedge_self (u : Minkowski13) : nativeWedge u u = 0 := by
  exact (exteriorPower.ιMulti ℝ 2).map_eq_zero_of_eq ![u, u]
    (i := 0) (j := 1) (by rfl) (by decide)

def boundaryBivector
    (z : InfoGeometry.Clifford.PolarizedMinkowski55.Boundary55) : Bivector13 :=
  nativeWedge z.1.2 z.2.2

theorem pairSwap_bivector
    (z : InfoGeometry.Clifford.PolarizedMinkowski55.Boundary55) :
    bivectorReadout (boundaryBivector
      (InfoGeometry.Clifford.PolarizedMinkowski55.pairSwap z)) =
      -bivectorReadout (boundaryBivector z) := by
  simpa [boundaryBivector, pairSwap] using
    wedgeCoefficients_swap z.1.2 z.2.2

theorem mixedSwap_bivector
    (z : InfoGeometry.Clifford.PolarizedMinkowski55.Boundary55) :
    bivectorReadout (boundaryBivector
      (InfoGeometry.Clifford.PolarizedMinkowski55.mixedSwap z)) =
      -bivectorReadout (boundaryBivector z) := by
  simp only [boundaryBivector, bivectorReadout_wedge]
  funext i
  fin_cases i <;> simp [mixedSwap, vectorFlip, pairSwap, wedgeCoefficients] <;> ring

theorem mixedSwap_hodge
    (z : InfoGeometry.Clifford.PolarizedMinkowski55.Boundary55) :
    hodgeStar (bivectorReadout (boundaryBivector
      (InfoGeometry.Clifford.PolarizedMinkowski55.mixedSwap z))) =
      -hodgeStar (bivectorReadout (boundaryBivector z)) := by
  rw [mixedSwap_bivector]
  funext i
  fin_cases i <;> simp [hodgeStar]

def spatialParity (u : Minkowski13) : Minkowski13 := (u.1, -u.2)

def twoFormParity (F : TwoFormC) : TwoFormC :=
  ![-F 0, -F 1, -F 2, F 3, F 4, F 5]

theorem spatialParity_wedge (u v : Minkowski13) :
    wedgeCoefficients (spatialParity u) (spatialParity v) =
      twoFormParity (wedgeCoefficients u v) := by
  funext i
  fin_cases i <;> simp [wedgeCoefficients, spatialParity, twoFormParity] <;> ring

theorem spatialParity_hodge (F : TwoFormC) :
    hodgeStar (twoFormParity F) = -twoFormParity (hodgeStar F) := by
  funext i
  fin_cases i <;> simp [twoFormParity, hodgeStar]

theorem spatialParity_selfDual (F : TwoFormC) :
    selfDualPart (twoFormParity F) = twoFormParity (antiSelfDualPart F) := by
  funext i
  fin_cases i <;>
    simp [selfDualPart, antiSelfDualPart, twoFormParity, hodgeStar] <;> ring

theorem spatialParity_antiSelfDual (F : TwoFormC) :
    antiSelfDualPart (twoFormParity F) = twoFormParity (selfDualPart F) := by
  funext i
  fin_cases i <;>
    simp [selfDualPart, antiSelfDualPart, twoFormParity, hodgeStar] <;> ring

theorem bivector_chiral_reconstruction (B : Bivector13) :
    selfDualPart (bivectorReadout B) + antiSelfDualPart (bivectorReadout B) =
      bivectorReadout B := by
  exact self_plus_anti (bivectorReadout B)

end InfoGeometry.Geometry.PolarizedBoundaryBivectors
