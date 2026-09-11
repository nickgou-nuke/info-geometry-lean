import InfoGeometry.Clifford.PolarizedBoundaryInvolutions
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HodgeStar4DFinite
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Actual exterior bivectors and the existing Lorentzian Hodge readout

Four-vectors are not Weyl spinors. Their alternating product belongs to the
native second exterior power. The coordinate readout is induced by its
universal property, with the repository's order `(01,02,03,23,31,12)`.

The six-component complex Hodge operator is reused as-is. Its geometric
identification with a metric-derived bundle Hodge star is not assumed here.
A spacetime orientation reversal swaps its complex chiral sectors. The
source's interchange of two vector slots instead negates their bivector.
Neither operation is automatically a curvature or a modular conjugation.
-/

noncomputable section

namespace InfoGeometry.Geometry.PolarizedBoundaryBivectors
open scoped BigOperators

open InfoGeometry.Twistor.Cl55MinkowskiCelestialSlice
open InfoGeometry.Clifford.PolarizedMinkowski55
open InfoGeometry.Clifford.PolarizedBoundaryInvolutions
open InfoGeometry.Canonical.HodgeStar4DFinite

abbrev Bivector13 := ⋀[ℝ]^2 Minkowski13

/-- The native exterior product, not a six-field surrogate. -/
def nativeWedge (u v : Minkowski13) : Bivector13 := exteriorPower.ιMulti ℝ 2 ![u, v]

/-- Complexification of the real bivector coefficients in the existing Hodge ordering. -/
def wedgeCoefficients (u v : Minkowski13) : TwoFormC :=
  ![((u.1 * v.2 0 - u.2 0 * v.1 : ℝ) : ℂ),
    ((u.1 * v.2 1 - u.2 1 * v.1 : ℝ) : ℂ),
    ((u.1 * v.2 2 - u.2 2 * v.1 : ℝ) : ℂ),
    ((u.2 1 * v.2 2 - u.2 2 * v.2 1 : ℝ) : ℂ),
    ((u.2 2 * v.2 0 - u.2 0 * v.2 2 : ℝ) : ℂ),
    ((u.2 0 * v.2 1 - u.2 1 * v.2 0 : ℝ) : ℂ)]

@[simp] theorem wedgeCoefficients_self (u : Minkowski13) : wedgeCoefficients u u = 0 := by
  funext i
  fin_cases i <;> simp [wedgeCoefficients, mul_comm]

theorem wedgeCoefficients_swap (u v : Minkowski13) :
    wedgeCoefficients v u = -wedgeCoefficients u v := by
  funext i
  fin_cases i <;> simp [wedgeCoefficients] <;> ring

/-- Alternating map whose universal extension reads coefficients of genuine exterior elements. -/
def coefficientAlternating : AlternatingMap ℝ Minkowski13 TwoFormC (Fin 2) where
  toFun m := wedgeCoefficients (m 0) (m 1)
  map_update_add' m i u v := by
    fin_cases i <;> funext j <;> fin_cases j <;>
      simp [wedgeCoefficients, Function.update] <;> ring
  map_update_smul' m i r u := by
    fin_cases i <;> funext j <;> fin_cases j <;>
      simp [wedgeCoefficients, Function.update] <;> ring
  map_eq_zero_of_eq' m i j hij hne := by
    have h01 : m 0 = m 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    simpa only [h01] using wedgeCoefficients_self (m 1)

/-- Native universal-property map out of the degree-two exterior power. -/
def bivectorReadout : Bivector13 →ₗ[ℝ] TwoFormC :=
  exteriorPower.alternatingMapLinearEquiv coefficientAlternating

@[simp] theorem bivectorReadout_wedge (u v : Minkowski13) :
    bivectorReadout (nativeWedge u v) = wedgeCoefficients u v := by
  rw [bivectorReadout, nativeWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Self-annihilation is the exterior alternating law, not a field equation. -/
theorem nativeWedge_self (u : Minkowski13) : nativeWedge u u = 0 := by
  exact (exteriorPower.ιMulti ℝ 2).map_eq_zero_of_eq ![u, u]
    (i := 0) (j := 1) (by rfl) (by decide)

/-- The source's two vector slots give one mixed bivector. -/
def boundaryBivector (z : Boundary55) : Bivector13 := nativeWedge z.1.2 z.2.2

/-- Swapping the two rays negates the mixed bivector coefficients. -/
theorem pairSwap_bivector (z : Boundary55) :
    bivectorReadout (boundaryBivector (pairSwap z)) =
      -bivectorReadout (boundaryBivector z) := by
  simpa [boundaryBivector, pairSwap] using wedgeCoefficients_swap z.1.2 z.2.2

/-- Negating both vectors and exchanging them has the same alternating sign. -/
theorem mixedSwap_bivector (z : Boundary55) :
    bivectorReadout (boundaryBivector (mixedSwap z)) =
      -bivectorReadout (boundaryBivector z) := by
  simp only [boundaryBivector, bivectorReadout_wedge]
  funext i
  fin_cases i <;> simp [mixedSwap, vectorFlip, pairSwap, wedgeCoefficients] <;> ring

/-- For this state-slot operation the finite Hodge map simply transports that minus sign. -/
theorem mixedSwap_hodge (z : Boundary55) :
    hodgeStar (bivectorReadout (boundaryBivector (mixedSwap z))) =
      -hodgeStar (bivectorReadout (boundaryBivector z)) := by
  rw [mixedSwap_bivector]
  funext i
  fin_cases i <;> simp [hodgeStar]

/-- Spatial inversion of the four-vector, distinct from swapping two state slots. -/
def spatialParity (u : Minkowski13) : Minkowski13 := (u.1, -u.2)

/-- Its induced action on the six coefficient slots. -/
def twoFormParity (F : TwoFormC) : TwoFormC :=
  ![-F 0, -F 1, -F 2, F 3, F 4, F 5]

theorem spatialParity_wedge (u v : Minkowski13) :
    wedgeCoefficients (spatialParity u) (spatialParity v) =
      twoFormParity (wedgeCoefficients u v) := by
  funext i
  fin_cases i <;> simp [wedgeCoefficients, spatialParity, twoFormParity] <;> ring

/-- Orientation reversal anti-commutes with the chosen Lorentzian star. -/
theorem spatialParity_hodge (F : TwoFormC) :
    hodgeStar (twoFormParity F) = -twoFormParity (hodgeStar F) := by
  funext i
  fin_cases i <;> simp [twoFormParity, hodgeStar]

/-- Complex +i and -i sectors are exchanged by spatial parity. -/
theorem spatialParity_selfDual (F : TwoFormC) :
    selfDualPart (twoFormParity F) = twoFormParity (antiSelfDualPart F) := by
  funext i
  fin_cases i <;> simp [selfDualPart, antiSelfDualPart, twoFormParity, hodgeStar] <;> ring

theorem spatialParity_antiSelfDual (F : TwoFormC) :
    antiSelfDualPart (twoFormParity F) = twoFormParity (selfDualPart F) := by
  funext i
  fin_cases i <;> simp [selfDualPart, antiSelfDualPart, twoFormParity, hodgeStar] <;> ring

/-- The existing complex chiral projections reconstruct the native exterior readout. -/
theorem bivector_chiral_reconstruction (B : Bivector13) :
    selfDualPart (bivectorReadout B) + antiSelfDualPart (bivectorReadout B) =
      bivectorReadout B := by
  exact self_plus_anti (bivectorReadout B)

/-- Scalar coefficients symmetric in two indices cannot create an antisymmetric field. -/
theorem symmetric_scalar_contraction_zero
    (u : Fin 4 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : ∀ i j, F i j = -F j i) :
    ∑ i, ∑ j, u i * u j * F i j = 0 := by
  have hswap : (∑ i, ∑ j, u i * u j * F i j) =
      -(∑ i, ∑ j, u i * u j * F i j) := by
    calc
      _ = ∑ j, ∑ i, u i * u j * F i j := Finset.sum_comm
      _ = -(∑ j, ∑ i, u j * u i * F j i) := by
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [hF i j]
        ring
  linarith

end InfoGeometry.Geometry.PolarizedBoundaryBivectors
