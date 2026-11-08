/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AttentionPolarizedSinkhornBridge
import InfoGeometry.QuantumContext.MarkovAttentionGroupInverse
import InfoGeometry.QuantumContext.MarkovAttentionWeightedRange

/-!
# Stationary weights and Poisson solvability for polarized attention

This candidate specializes the existing finite positive Markov results to the
Gibbs-row matrix `polarizedPlusAttentionMatrix`. Stationarity uses the row-weight
convention `∑ i, π i * P i j = π j`; observables are column vectors acted on by
`P *ᵥ x`. The source and solution criteria below are finite-dimensional and
make no detailed-balance or iterate-convergence claim.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

open InfoGeometry.Canonical.Attention
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.Attention

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance polarizedAttentionFinNonempty : Nonempty (Fin n) :=
  ⟨⟨0, Fact.out⟩⟩

/-- The transition matrix owned by the polarized Sinkhorn bridge. -/
abbrev transition (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β

/-- Polarized Gibbs attention has a unique strictly positive normalized
stationary row distribution. The stationarity convention is
`∑ i, π i * transition i j = π j`, so `π` is a left stationary weight while
`transition *ᵥ x` acts on column observables. -/
theorem existsUnique_positive_normalized_stationary_row
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) :
    ∃! π : Fin n → ℝ,
      (∀ i, 0 < π i) ∧
      (∑ i, π i = 1) ∧
      (∀ j, ∑ i, π i * transition (E := E) (V := V) queries ctx β i j = π j) := by
  exact MarkovDrazin.existsUnique_positive_normalized_stationary_row
    (transition (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_pos
      (E := E) (V := V) queries ctx β)

/-- The range of the polarized-attention Laplacian is exactly the kernel of
the stationary weighted mean. The hypotheses explicitly provide a normalized
left stationary weight; no reversibility assumption is used. -/
theorem range_laplacian_eq_weightedMean_ker
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (π : Fin n → ℝ)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * transition (E := E) (V := V) queries ctx β i j = π j) :
    LinearMap.range (Matrix.toLin' (1 - transition (E := E) (V := V) queries ctx β)) =
      LinearMap.ker (MarkovDrazin.weightedMeanMap π) := by
  exact MarkovDrazin.range_laplacian_eq_weightedMean_ker
    (transition (E := E) (V := V) queries ctx β) π
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_pos
      (E := E) (V := V) queries ctx β)
    hπsum hstat

/-- For the actual polarized transition, the Drazin principal kernel
projector is the constant-valued stationary-mean map. This identifies the
spectral projector with the left stationary distribution while keeping the
column-observable and row-weight conventions explicit. -/
theorem principalProjector_apply_eq_weightedMean
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (π : Fin n → ℝ)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * transition (E := E) (V := V) queries ctx β i j = π j)
    (D : Module.End ℝ (Fin n → ℝ))
    (hD : IsGroupInverse
      (Matrix.toLin' (1 - transition (E := E) (V := V) queries ctx β)) D)
    (x : Fin n → ℝ) :
    principalIdempotent
        (Matrix.toLin' (1 - transition (E := E) (V := V) queries ctx β)) D x =
      fun _ => weightedMeanMap π x := by
  exact principalIdempotent_eq_stationaryMean_projection
    (transition (E := E) (V := V) queries ctx β) π
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_pos
      (E := E) (V := V) queries ctx β)
    hπsum hstat D hD x

/-- A zero stationary weighted mean is precisely the source condition for the
polarized-attention Poisson equation. The group inverse supplies the canonical
solution in the Laplacian range, where the solution is unique. -/
theorem poisson_solution_of_weightedMean_zero
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (π b : Fin n → ℝ)
    (hπsum : ∑ i, π i = 1)
    (hstat : ∀ j, ∑ i, π i * transition (E := E) (V := V) queries ctx β i j = π j)
    (hb : MarkovDrazin.weightedMeanMap π b = 0) :
    ∃ D : Module.End ℝ (Fin n → ℝ),
      IsGroupInverse (Matrix.toLin' (1 - transition (E := E) (V := V) queries ctx β)) D ∧
      Matrix.toLin' (1 - transition (E := E) (V := V) queries ctx β) (D b) = b ∧
      D b ∈ (Matrix.toLin' (1 - transition (E := E) (V := V) queries ctx β)).range ∧
      ∀ x : Fin n → ℝ,
        x ∈ (Matrix.toLin' (1 - transition (E := E) (V := V) queries ctx β)).range →
        Matrix.toLin' (1 - transition (E := E) (V := V) queries ctx β) x = b →
        x = D b := by
  exact MarkovDrazin.stochastic_laplacian_poisson_solution_of_weightedMean_zero
    (transition (E := E) (V := V) queries ctx β) π
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_pos
      (E := E) (V := V) queries ctx β)
    hπsum hstat b hb

end InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention
