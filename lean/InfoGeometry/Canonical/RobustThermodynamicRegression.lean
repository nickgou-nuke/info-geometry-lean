/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Basic

/-!
# Robust Thermodynamic Regression (RTR) 

This module formalizes the thermodynamic learning paradigm as a 
gauge-invariant inference process over an informational manifold.
It serves as the formal proof backbone for the `thermofit` Python package.
-/

open scoped BigOperators
open Matrix

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
/-- Definition `FisherStiffness`. -/
def FisherStiffness (p : Data → ℝ) (Hi : Data → Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  ∑ i : Data, p i • Hi i

-- Fluctuation Pressure (B): The variance of informational gradients.
-- B = (1/ε) * Cov_p(∇ E)
-- We define it here simply as a symmetric matrix representing this pressure.
/-- Definition `FluctuationPressure`. -/
noncomputable def FluctuationPressure (p : Data → ℝ) (gi : Data → Fin k → ℝ) (ε : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  -- B_ab = (1/ε) * Σ p_i * (g_ia - g_avg_a)(g_ib - g_avg_b)
  let g_avg : Fin k → ℝ := fun a => ∑ i : Data, p i * gi i a
  fun a b => (1 / ε) * ∑ i : Data, p i * (gi i a - g_avg a) * (gi i b - g_avg b)

-- Exact Hessian: H = A - B
/-- Definition `ExactHessian`. -/
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
  (h_unstable : ∃ x : Fin k →₀ ℝ, x ≠ 0 ∧ (x.sum fun i xi => x.sum fun j xj => xi * B i j * xj) ≥ (x.sum fun i xi => x.sum fun j xj => xi * A i j * xj)) :
  ¬ IsResolvable k (ExactHessian k A B) :=
by
  intro h_resolvable
  unfold IsResolvable ExactHessian at h_resolvable
  rcases h_unstable with ⟨x, hx_nonzero, hB_ge_A⟩
  
  -- From H being PosDef (which means H.IsHermitian ∧ 0 < x' H x for Finsupp x)
  have h_H_pos : 0 < x.sum fun i xi => x.sum fun j xj => star xi * (A - B) i j * xj :=
    h_resolvable.right hx_nonzero
  
  -- Re-state the target subtraction equality
  have h_sum_sub : (x.sum fun i xi => x.sum fun j xj => star xi * (A - B) i j * xj) =
    (x.sum fun i xi => x.sum fun j xj => xi * A i j * xj) - (x.sum fun i xi => x.sum fun j xj => xi * B i j * xj) := by
    simp [Matrix.sub_apply, Finsupp.sum_sub, mul_sub, sub_mul]
  
  rw [h_sum_sub] at h_H_pos
  -- Now we have 0 < (x' A x) - (x' B x), so (x' A x) > (x' B x)
  have h_A_gt_B : (x.sum fun i xi => x.sum fun j xj => xi * A i j * xj) > (x.sum fun i xi => x.sum fun j xj => xi * B i j * xj) :=
    sub_pos.mp h_H_pos
    
  -- But our instability hypothesis says B >= A. Contradiction!
  linarith

end FUSION
