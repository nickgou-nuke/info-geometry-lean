import Mathlib
import proofs.KreinDoubling
import proofs.StructureTensor

open Matrix

abbrev Spinor := Fin 2 ⊕ Fin 2 → ℝ

/-!
# Nambu-Gorkov Spinors in Image Geometry

This module formalizes the conceptual mapping from Nambu-Gorkov spinors 
(used in superconductivity to unify creation and annihilation operators)
to the information geometry of images. 

In this formalism:
- The top half of the spinor (v) represents the signal "creation" (gradient).
- The bottom half (v*) represents the signal "annihilation" or background.

The structural flow is driven by the Cartan-Krein Doubled structure tensor, 
which we prove to be self-adjoint (Hermitian) with respect to the 
indefinite Krein metric.
-/

/-- The fundamental indefinite (2,2) Krein metric. -/
def kreinMetric : Matrix4x4 :=
  fromBlocks 1 0 0 (-1)

/-- The Krein adjoint of an operator K is J * Kᵀ * J -/
def kreinAdjoint (K : Matrix4x4) : Matrix4x4 :=
  kreinMetric * Kᵀ * kreinMetric

/-- 
Theorem: A Cartan-Krein Doubled patch is exactly self-adjoint in the Krein space!
This is the ultimate proof that the diffusion flow preserves the causal 
structure of the structural tensors.
-/
theorem kreinDoubling_is_krein_hermitian (M : Patch2x2) :
    kreinAdjoint (kreinDoubling M) = kreinDoubling M := by
  dsimp [kreinAdjoint, kreinDoubling, kreinMetric]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [fromBlocks, symmPart, skewPart, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- 
The indefinite Krein inner product between two Nambu-Gorkov spinors.
Returns the difference between the structural alignment and background correlation.
-/
def kreinInnerProduct (Ψ Φ : Spinor) : ℝ :=
  dotProduct Ψ (kreinMetric.mulVec Φ)
