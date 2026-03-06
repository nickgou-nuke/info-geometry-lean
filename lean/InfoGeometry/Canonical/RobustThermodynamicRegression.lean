/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Robust Thermodynamic Regression (RTR) 

This module formalizes the thermodynamic learning paradigm as a 
gauge-invariant inference process over an informational manifold.
It serves as the formal proof backbone for the `thermofit` Python package.
-/

open scoped BigOperators

namespace FUSION

-- Define abstract sets for our Data and Parameter space
variable {Data : Type} [Fintype Data] [Nonempty Data]
variable {Theta : Type}

/-- 
The Informational Energy of a data point given parameters θ.
In the application, E(i, θ) = KL(y_i || h(x_i; θ)).
-/
def Energy (E : Data → Theta → ℝ) := E

/-- 
The Thermodynamic Partition Function: Z(θ, ε) = Σ exp(-E_i / ε)
-/
noncomputable def partitionFunction (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) : ℝ :=
  ∑ i : Data, Real.exp (- E i θ / ε)

/-- 
The Free Energy Potential: F(θ, ε) = - ε * ln Z
This is the Fenchel-Legendre dual potential we minimize in `thermofit`.
-/
noncomputable def freeEnergy (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) : ℝ :=
  - ε * Real.log (partitionFunction E θ ε)

/-- 
Gibbs Probability Measure: p_i = exp(-E_i / ε) / Z
The thermodynamic weights that reject outliers automatically.
-/
noncomputable def gibbsWeights (E : Data → Theta → ℝ) (θ : Theta) (ε : ℝ) (i : Data) : ℝ :=
  Real.exp (- E i θ / ε) / (partitionFunction E θ ε)

/-! ## The Information-Theoretic Hessian Decomposition -/

variable (k : ℕ)

-- Structural Stiffness (A): The expected informational curvature.
-- A = E_p[∇^2 E]
def FisherStiffness (p : Data → ℝ) (Hi : Data → Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  ∑ i : Data, p i • Hi i

-- Fluctuation Pressure (B): The variance of informational gradients.
-- B = (1/ε) * Cov_p(∇ E)
-- We define it here simply as a symmetric matrix representing this pressure.
def FluctuationPressure (p : Data → ℝ) (gi : Data → Fin k → ℝ) (ε : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  -- B_ab = (1/ε) * Σ p_i * (g_ia - g_avg_a)(g_ib - g_avg_b)
  let g_avg : Fin k → ℝ := fun a => ∑ i : Data, p i * gi i a
  fun a b => (1 / ε) * ∑ i : Data, p i * (gi i a - g_avg a) * (gi i b - g_avg b)

-- Exact Hessian: H = A - B
def ExactHessian (A B : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  A - B

/-! ## The Fundamental Theorem of RTR Stability -/

/-- 
Stability Lemma:
The informational manifold is stable (Resolvable) if the exact Hessian 
is Positive Definite. This prevents the Fold Catastrophe.
-/
def IsResolvable (H : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  H.PosDef

/-- 
Theorem: The Thermodynamic Phase Transition
If the fluctuation pressure (noise) overcomes the structural stiffness, 
the system undergoes a catastrophe, losing resolvability.
-/
theorem phase_transition_catastrophe
  (A B : Matrix (Fin k) (Fin k) ℝ)
  (hA : A.PosDef)
  (h_unstable : ∃ v : Fin k → ℝ, v ≠ 0 ∧ Matrix.dotProduct v (B *ᵥ v) ≥ Matrix.dotProduct v (A *ᵥ v)) :
  ¬ IsResolvable k (ExactHessian k A B) :=
by
  intro h_resolvable
  unfold IsResolvable ExactHessian at h_resolvable
  rcases h_unstable with ⟨v, hv_nonzero, hB_ge_A⟩
  
  -- From H being PosDef, we must have v^T H v > 0 for all non-zero v
  have h_H_pos := h_resolvable.2 v hv_nonzero
  
  -- Expand v^T H v = v^T (A - B) v
  -- Matrix.dotProduct is linear, so v^T (A - B) v = v^T A v - v^T B v
  rw [Matrix.sub_mulVec, Matrix.dotProduct_sub] at h_H_pos
  
  -- We have v^T A v - v^T B v > 0, which implies v^T A v > v^T B v
  have h_A_gt_B : Matrix.dotProduct v (B *ᵥ v) < Matrix.dotProduct v (A *ᵥ v) := sub_pos.mp h_H_pos
  
  -- This directly contradicts hB_ge_A (v^T B v >= v^T A v)
  linarith

end FUSION
