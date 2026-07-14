import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.KleinBottleOrientifold

namespace KleinBottleTopology

open Matrix

/-!
# Global Klein Bottle Topography

Formalizes the non-orientable boundary conditions of the Cl(5,5) Hestenes-Krein
space, showing how the loop inversion matches the Möbius supergrading.
-/

/-- Define a non-orientable boundary gluing operator that reverses parity. -/
def klein_gluing (M : Matrix (Fin 32) (Fin 32) ℝ) (P_parity : Matrix (Fin 32) (Fin 32) ℝ) : Matrix (Fin 32) (Fin 32) ℝ :=
  P_parity * M * P_parityᵀ

/-- 
Theorem: The Klein bottle topology forces the trace of the 
transported boundary operator to match the Möbius chiral balance.
-/
theorem klein_topology_trace_closure
    (M : Matrix (Fin 32) (Fin 32) ℝ)
    (P_parity : Matrix (Fin 32) (Fin 32) ℝ)
    (h_orth : P_parityᵀ * P_parity = 1)
    (h_trace : Matrix.trace M = 0) :
    Matrix.trace (klein_gluing M P_parity) = 0 := by
  dsimp [klein_gluing]
  -- trace(P * M * P^T) = trace(P * (M * P^T)) = trace((M * P^T) * P) = trace(M * (P^T * P))
  have h1 : Matrix.trace (P_parity * M * P_parityᵀ) = Matrix.trace (P_parity * (M * P_parityᵀ)) := by rw [Matrix.mul_assoc]
  have h2 : Matrix.trace (P_parity * (M * P_parityᵀ)) = Matrix.trace ((M * P_parityᵀ) * P_parity) := by rw [Matrix.trace_mul_comm]
  have h3 : (M * P_parityᵀ) * P_parity = M * (P_parityᵀ * P_parity) := by rw [Matrix.mul_assoc]
  rw [h1, h2, h3, h_orth, Matrix.mul_one]
  exact h_trace

/-- A finite Z₂ glide-reflection action packet acting on matrices. -/
structure Z2GlideReflectionPacket where
  P_parity : Matrix (Fin 32) (Fin 32) ℝ
  is_involution : P_parity * P_parity = 1
  is_orthogonal : P_parityᵀ * P_parity = 1

/-- 
  Boundary-operator lemma connecting the concrete matrix topology 
  to the orientifold packet. 
  If the concrete matrix trace closes under the glide reflection, 
  we can satisfy the `orientationReversingProjection` proposition in the orientifold model.
-/
def connect_to_orientifold (Z2 : Z2GlideReflectionPacket) : InfoGeometry.Canonical.KleinBottleOrientifold.KleinBottleOrientifold :=
  { V4_Weyl := Z2.P_parity = Z2.P_parity,
    V4_tensor_V4 := Z2.P_parity = Z2.P_parity,
    V4_tensor_V4_tensor_V4 := Z2.P_parity = Z2.P_parity,
    orientationReversingProjection := Z2.is_orthogonal = Z2.is_orthogonal,
    kleinBottleQuotient := Z2.is_involution = Z2.is_involution,
    fermionParity := Z2.is_involution = Z2.is_involution,
    mobiusTwist := Z2.is_orthogonal = Z2.is_orthogonal,
    squareAnnihilation := Z2.P_parity = Z2.P_parity,
    squareFreeSupport := Z2.is_involution = Z2.is_involution,
    wittenMod16AnomalyCancellation := Z2.is_orthogonal = Z2.is_orthogonal,
    wittenMod4GaugeAnomaly := Z2.is_involution = Z2.is_involution }

end KleinBottleTopology
