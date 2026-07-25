import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
open Nat
open scoped BigOperators

namespace InfoGeometry.Instanton

/-- Truncated vortex partition function for U(1) gauge theory with N_f=0 (pure gauge) up to order N.
The vortex partition function is given by
Z_N(ε₁, ε₂, q) = ∑_{k=0}^N (q/(ε₁ ε₂))^k / (k!)^2.
This is symmetric under exchange ε₁ ↔ ε₂ because it depends only on the product ε₁ ε₂.
-/
noncomputable def vortexPartitionAux (N : ℕ) (q ε₁ ε₂ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), ((q / (ε₁ * ε₂)) ^ k) / ((Nat.factorial k : ℝ) ^ 2)

lemma vortexPartitionSymmetric (N : ℕ) (q ε₁ ε₂ : ℝ) :
    vortexPartitionAux N q ε₁ ε₂ = vortexPartitionAux N q ε₂ ε₁ :=
  have h₁ : ∀ (k : ℕ), ( (q / (ε₁ * ε₂)) ^ k : ℝ) = ( (q / (ε₂ * ε₁)) ^ k : ℝ) := by
    intro k
    rw [mul_comm ε₁ ε₂]
  calc
    vortexPartitionAux N q ε₁ ε₂ =
        ∑ k ∈ Finset.range (N + 1), ((q / (ε₁ * ε₂)) ^ k) / ((Nat.factorial k : ℝ) ^ 2) := rfl
    _ = ∑ k ∈ Finset.range (N + 1), ((q / (ε₂ * ε₁)) ^ k) / ((Nat.factorial k : ℝ) ^ 2) := by
      apply Finset.sum_congr
      · rfl
      · intro k _
        rw [h₁ k]
    _ = vortexPartitionAux N q ε₂ ε₁ := rfl

/-- For the concrete case N = 3, we can compute the polynomial explicitly and check symmetry. -/
example : vortexPartitionAux 3 2 3 5 = vortexPartitionAux 3 2 5 3 :=
  vortexPartitionSymmetric 3 2 3 5

end InfoGeometry.Instanton
