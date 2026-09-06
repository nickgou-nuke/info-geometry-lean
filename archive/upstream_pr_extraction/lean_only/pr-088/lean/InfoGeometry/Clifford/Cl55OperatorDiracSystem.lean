import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Clifford.OperatorValuedJones

/-!
# The `Cl(5,5)` gamma basis as a strict Dirac-matrix system

The generic operator-coordinate layer deliberately separates matrix expansion
from the Clifford theorem boundary.  This file crosses that boundary for the
existing recursive `Cl(5,5)` spinor representation.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55OperatorDiracSystem

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.CliffordTower

/-- The bilinear metric represented by the recursive `Cl(5,5)` gamma basis. -/
noncomputable def gammaBasisMetric55 (i j : Fin 10) : ℝ :=
  (1 / 2 : ℝ) *
    QuadraticMap.polar (SplitQuad 5)
      (vec55SplitEquiv (vec55Basis i))
      (vec55SplitEquiv (vec55Basis j))

/-- The ten recursive gamma generators satisfy the strict metric anticommutator law. -/
theorem gammaBasis55_isDiracMatrixSystem :
    IsDiracMatrixSystem gammaBasisMetric55 gammaBasis55 := by
  intro i j
  unfold operatorAnticommutator
  rw [gammaBasis55, gammaBasis55, gamma55_anticomm]
  congr 1
  simp [gammaBasisMetric55]

/-- Readback of the strict Dirac relation for any two basis generators. -/
theorem gammaBasis55_anticommutator_eq_metric (i j : Fin 10) :
    operatorAnticommutator (gammaBasis55 i) (gammaBasis55 j) =
      algebraMap ℝ (SpinorMatrix 5) (2 * gammaBasisMetric55 i j) :=
  anticommutator_eq_metric gammaBasis55_isDiracMatrixSystem i j

end InfoGeometry.Clifford.Cl55OperatorDiracSystem
