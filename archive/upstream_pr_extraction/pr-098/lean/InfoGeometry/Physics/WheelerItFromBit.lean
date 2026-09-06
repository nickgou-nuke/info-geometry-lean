import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Physics.EmergentSpacetimeBilinear

/-!
# Wheeler's "It from Bit" and Emergent Spacetime Coordinates

This module formalizes John Archibald Wheeler's participatory cosmology in the
Krein-Clifford 32-dimensional framework:
1. `QuantumBit`: A binary idempotent projection operator ($P^2 = P$).
2. `ObserverState`: A state vector associated with the projective bit.
3. `itFromBitCoordinate`: Spacetime coordinates emerging from spinor bilinears.
4. `it_vanishes_for_zero_state`: The strict theorem "No bit => No it".
5. `emergentGravitationalMetric`: The quantum covariance metric tensor.
-/

namespace InfoGeometry.Physics.WheelerItFromBit

open InfoGeometry.Clifford.DyadicMorita
open InfoGeometry.Physics.EmergentSpacetime

/-- A primitive binary idempotent projection operator ($P^2 = P$). -/
structure QuantumBit where
  P : Mat32
  is_idempotent : P * P = P

/--
The classical spacetime coordinate $X_A(\psi) = \operatorname{Tr}(\rho_\eta(\psi) A)$
emerging from the Krein-bilinear expectation value of an operator $A \in M_{32}(\mathbb{R})$.
-/
def itFromBitCoordinate (psi : Spinor32) (A : Mat32) : ℝ :=
  spacetimeCoordinate psi A

/--
THEOREM 1 ("No Bit => No It"):
In the absence of an active state excitation ($\psi = 0$), all emergent
spacetime coordinates vanish identically.
-/
theorem it_vanishes_for_zero_state (A : Mat32) :
    itFromBitCoordinate 0 A = 0 := by
  have hdensity : kreinDensity 0 = 0 := by
    ext i j
    simp [kreinDensity, ketBra, kreinBra]
  simp [itFromBitCoordinate, spacetimeCoordinate, hdensity]

/--
The quantum information metric / covariance tensor for a general density matrix $\rho$:
$g_\rho(A, B) = \operatorname{Tr}(\rho A B) - \operatorname{Tr}(\rho A) \operatorname{Tr}(\rho B)$.
-/
def emergentGravitationalMetric (rho : Mat32) (A B : Mat32) : ℝ :=
  Matrix.trace (rho * A * B) - Matrix.trace (rho * A) * Matrix.trace (rho * B)

/--
THEOREM 2: Symmetry of the emergent metric for commuting observables.
-/
theorem emergentGravitationalMetric_comm_symm
    (rho A B : Mat32) (h_comm : A * B = B * A) :
    emergentGravitationalMetric rho A B = emergentGravitationalMetric rho B A := by
  dsimp [emergentGravitationalMetric]
  have hAB : rho * A * B = rho * B * A := by
    calc
      rho * A * B = rho * (A * B) := mul_assoc rho A B
      _ = rho * (B * A) := by rw [h_comm]
      _ = rho * B * A := (mul_assoc rho B A).symm
  rw [hAB, mul_comm (Matrix.trace (rho * A))]

end InfoGeometry.Physics.WheelerItFromBit
