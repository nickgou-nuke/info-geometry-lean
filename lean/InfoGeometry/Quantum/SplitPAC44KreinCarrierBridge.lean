import InfoGeometry.Algebra.Zorn.SplitOctonionGlobalWittNorm
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.DualFlatKreinGraph

/-!
# Split `(4,4)` carrier as a primal/dual neutral carrier

The null coordinates are `u = x + y` and `v = x - y`.  The map below uses
the Euclidean inner product only to turn the dual coordinate into a genuine
linear covector; it does not identify octonion multiplication with the
carrier action.
-/

namespace InfoGeometry.Quantum.SplitPAC44KreinCarrierBridge

open ProjectiveAffineConformalClosure55
open InfoGeometry.Quantum.DualFlatKreinGraph
open scoped InnerProductSpace

noncomputable def coordinateVector (X : PACSplit44) : Vector 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm ![
    X.x0 + X.y0, X.x1 + X.y1, X.x2 + X.y2, X.x3 + X.y3]

noncomputable def coordinateDualVector (X : PACSplit44) : Vector 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm ![
    X.x0 - X.y0, X.x1 - X.y1, X.x2 - X.y2, X.x3 - X.y3]

noncomputable def coordinateCovector (v : Vector 4) : Covector 4 where
  toFun w := ⟪v, w⟫_ℝ
  map_add' w z := inner_add_right v w z
  map_smul' c w := real_inner_smul_right v w c

noncomputable def pacToCarrier (X : PACSplit44) : Carrier 4 :=
  (coordinateVector X, coordinateCovector (coordinateDualVector X))

def Q44Polar (X Y : PACSplit44) : ℝ :=
  X.x0 * Y.x0 + X.x1 * Y.x1 + X.x2 * Y.x2 + X.x3 * Y.x3 -
    (X.y0 * Y.y0 + X.y1 * Y.y1 + X.y2 * Y.y2 + X.y3 * Y.y3)

theorem pacToCarrier_neutral_Q44Polar (X Y : PACSplit44) :
    neutralPair (pacToCarrier X) (pacToCarrier Y) = Q44Polar X Y := by
  cases X
  cases Y
  simp [neutralPair, pacToCarrier, coordinateVector, coordinateDualVector,
    coordinateCovector, Q44Polar,
    EuclideanSpace.equiv, PiLp.inner_apply, dotProduct,
    Fin.sum_univ_succ]
  ring_nf

theorem pacToCarrier_Q44 (X : PACSplit44) :
    neutralPair (pacToCarrier X) (pacToCarrier X) = Q44 X := by
  rw [pacToCarrier_neutral_Q44Polar]
  cases X
  simp [Q44Polar, ProjectiveAffineConformalClosure55.Q44]
  ring

end InfoGeometry.Quantum.SplitPAC44KreinCarrierBridge
