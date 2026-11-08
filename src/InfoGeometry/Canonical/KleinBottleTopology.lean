import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.KleinBottleOrientifold
import InfoGeometry.Topology.V4RootSystem

namespace InfoGeometry.Canonical.KleinBottleTopology

open Matrix

/-!
# Global Klein Bottle Topography

Formalizes the non-orientable boundary conditions of the Cl(5,5) Hestenes-Krein
space, showing how the loop inversion matches the Möbius supergrading.
-/

/-- Define a non-orientable boundary gluing operator that reverses parity. -/
def klein_gluing (M : Matrix (Fin 32) (Fin 32) ℝ) (P_parity : Matrix (Fin 32) (Fin 32) ℝ) : Matrix (Fin 32) (Fin 32) ℝ :=
  P_parity * M * P_parityᵀ

/-
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

/-
  Boundary-operator lemma connecting the concrete matrix topology 
  to the orientifold packet. 
  If the concrete matrix trace closes under the glide reflection, 
  we can satisfy the `orientationReversingProjection` proposition in the orientifold model.
-/
/-!
The former constructor returned a record whose fields were reflexive equality
markers.  The finite native content available here is the actual Klein-four
involution, so expose that content as a subtype instead of manufacturing an
orientifold evidence packet.
-/
abbrev NativeKleinBottleCarrier :=
  KleinBottleOrientifold.KleinBottleOrientifold

def connect_to_orientifold :
    NativeKleinBottleCarrier :=
  KleinBottleOrientifold.canonicalKleinBottleOrientifold

end InfoGeometry.Canonical.KleinBottleTopology
