import Mathlib.Tactic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import InfoGeometry.Meta.Architecture
import InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit

/-!
# InfoGeometry.Canonical.PrimeHurwitzCliffordCascadeLimit

Prime-specific Hurwitz--Clifford discrete wavelet cascade interface.

This file connects finite prime Lee--Yang approximants to a discrete
Hurwitz--Clifford cascade reconstruction.

It does not prove RH.

It formulates the exact analytic problem:
the renormalized finite prime partition functions must be realized as
Hurwitz--Clifford cascade partial sums, and those partial sums must converge
locally uniformly to the Cayley pullback of the completed `xi` function.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeHurwitzCliffordCascadeLimit

open InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
open InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit

/-- Prime-specific realization of the renormalized approximants as discrete
Hurwitz--Clifford cascade partial sums. -/
@[rep_depth operator]
structure PrimeHurwitzCliffordCascadeRealization
    (F : ParaunitaryCliffordFilterBank)
    (C : CliffordCascadeSystem F)
    (A : PrimeLeeYangApproximants)
    (Xi : CompletedXiFunction) where

  /-- Finite discrete cascade partial reconstruction. -/
  cascadePartial : ℕ → ℂ → ℂ

  /-- The finite cascade partial sums are exactly the renormalized approximants. -/
  partial_eq_renormZ :
    ∀ N z, cascadePartial N z = A.renormZ N z

  /-- Holomorphicity of the finite discrete cascade partial sums. -/
  holomorphicPartials :
    ∀ N, Differentiable ℂ (cascadePartial N)

  /-- Local boundedness needed for Montel/normal-family arguments. -/
  locallyUniformBounded :
    ∀ K : Set ℂ, IsCompact K →
      ∃ C : ℝ, ∀ N z, z ∈ K → ‖cascadePartial N z‖ ≤ C

  /-- Compact-uniform tail control on every compact subset of the Cayley chart. -/
  compactUniformTailControl :
    ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ N₀, ∀ m n, N₀ ≤ m → N₀ ≤ n →
        ∀ z, z ∈ K → ‖cascadePartial m z - cascadePartial n z‖ < ε

  /-- The candidate locally uniform cascade limit. -/
  cascadeLimit : ℂ → ℂ

  /-- Full cascade reconstruction equals the Cayley pullback of `xi`. -/
  reconstruction_eq_xi_cayley :
    ∀ z : ℂ,
      cascadeLimit z = Xi.xi (cayleyInv z)

  /-- Final Hurwitz-ready convergence statement to be proved by a concrete model. -/
  locallyUniformRenormalizedLimit :
    TendstoLocallyUniformly cascadePartial cascadeLimit Filter.atTop

end InfoGeometry.Canonical.PrimeHurwitzCliffordCascadeLimit
