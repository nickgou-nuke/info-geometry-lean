import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import Mathlib.LinearAlgebra.Pi

open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open Finset

noncomputable def projLeftZornPlus : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun x i := if i.val < 4 then x i else 0
  map_add' x y := by ext i; split <;> simp
  map_smul' c x := by ext i; split <;> simp

theorem circular_left_zornPlus :
    circularL zornPlus = projLeftZornPlus := by
  apply LinearMap.ext_pi
  intro j
  ext i
  simp only [LinearMap.comp_apply, LinearMap.stdBasis_apply]
  have h := circularL_zornPlus_diagonal j
  have h2 : circularCoordinateLinearEquiv (circularPeirceBasis j) = Pi.single j 1 := by
    ext k; simp [circularCoordinateLinearEquiv, circularPeirceBasis]
  -- we can use this
  sorry
