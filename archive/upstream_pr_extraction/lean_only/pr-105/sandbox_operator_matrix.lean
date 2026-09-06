import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
import Mathlib.Data.Matrix.Basic

open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open Finset

noncomputable def circularMatrix : Module.End ℝ Coord ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  LinearMap.toMatrixAlgEquiv (Pi.basisFun ℝ (Fin 8))

noncomputable def L_mat (a : CZ) : Matrix (Fin 8) (Fin 8) ℝ :=
  circularMatrix (circularL a)

noncomputable def R_mat (a : CZ) : Matrix (Fin 8) (Fin 8) ℝ :=
  circularMatrix (circularR a)

theorem circular_left_zornPlus_matrix :
    L_mat zornPlus = Matrix.diagonal (fun i => if i.val < 4 then 1 else 0) := by
  ext i j
  dsimp [L_mat, circularMatrix, LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix, circularL, circularOperatorReadout]
  -- here we will have (circularL zornPlus (Pi.single j 1)) i
  sorry
