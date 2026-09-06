import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

noncomputable def projLeftZornPlus : Coord →ₗ[ℝ] Coord where
  toFun x i := if i.val < 4 then x i else 0
  map_add' x y := by ext i; split <;> simp
  map_smul' c x := by ext i; split <;> simp

theorem circular_left_zornPlus : circularL zornPlus = projLeftZornPlus := by
  apply (Pi.basisFun ℝ (Fin 8)).ext
  intro i
  ext j
  have h1 : (Pi.basisFun ℝ (Fin 8)) i = circularCoordinateLinearEquiv (circularPeirceBasis i) := by
    ext k
    simp [circularCoordinateLinearEquiv, circularPeirceBasis]
  rw [h1]
  have h2 := circularL_zornPlus_diagonal i
  -- evaluate h2 at j
  sorry
