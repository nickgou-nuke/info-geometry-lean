import Mathlib.Tactic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import InfoGeometry.Meta.Architecture
import InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform
import InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit
import InfoGeometry.Canonical.PrimeHurwitzCliffordCascadeLimit

/-!
# InfoGeometry.Canonical.PrimeLaplaceMellinHurwitzWaveletLimit

Prime-specific Laplace--Mellin / Hurwitz--Clifford wavelet limit socket.

This file does not prove RH.

It formalizes the exact analytic problem:
renormalized finite prime Lee--Yang partition functions are discrete
Hurwitz--Clifford cascade partial reconstructions whose compact-uniform limit
is the Cayley pullback of the completed xi function.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLaplaceMellinHurwitzWaveletLimit

open InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
open InfoGeometry.Analysis.LaplaceMellinScaleShapeTransform
open InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit
open InfoGeometry.Canonical.PrimeHurwitzCliffordCascadeLimit

/-- Cayley inverse. -/
@[rep_depth operator]
def cayleyInv (z : ℂ) : ℂ :=
  z / (1 + z)

abbrev CompletedXiFunction := InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit.CompletedXiFunction

abbrev PrimeLeeYangApproximants :=
  InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit.PrimeLeeYangApproximants

/-- Renormalized approximant. -/
@[rep_depth operator]
def PrimeLeeYangApproximants.renormZ
    (A : PrimeLeeYangApproximants) (N : ℕ) (z : ℂ) : ℂ :=
  A.R N z * A.Z N z

/--
Prime-specific realization of the renormalized approximants as a discrete
Hurwitz--Clifford cascade with a scale/shape analytic packet.

This is the exact bridge requested by the architecture:
the prime approximants are not arbitrary functions; they are finite discrete
cascade reconstructions, and the scale/shape operator spine is kept separate
from the convergence claim.
-/
@[rep_depth operator]
structure PrimeHurwitzWaveletXiRealization
    (F : ParaunitaryCliffordFilterBank)
    (A : PrimeLeeYangApproximants)
    (Ξ : CompletedXiFunction) where
  scaleShape : LaplaceMellinScaleShapePacket
  cascade : CliffordCascadeSystem F

  /-- The prime signal reconstructed by the discrete cascade. -/
  primeSignal : CliffordCascadeSystem.Signal cascade

  /-- Finite cascade partial reconstructions. -/
  waveletPartial : ℕ → ℂ → ℂ

  /-- The finite cascade partial sums are exactly the renormalized approximants. -/
  partial_eq_renormZ :
    ∀ N z, waveletPartial N z = A.renormZ N z

  /-- Holomorphicity of the finite partial reconstructions on the Cayley chart. -/
  holomorphicPartials :
    ∀ N, Differentiable ℂ (waveletPartial N)

  /-- Local boundedness needed for Montel/normal-family arguments. -/
  locallyUniformBounded :
    ∀ K : Set ℂ, IsCompact K →
      ∃ C : ℝ, ∀ N z, z ∈ K → ‖waveletPartial N z‖ ≤ C

  /-- Compact-uniform tail control on every compact subset. -/
  compactUniformTailControl :
    ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ N₀, ∀ m n, N₀ ≤ m → N₀ ≤ n →
        ∀ z, z ∈ K → ‖waveletPartial m z - waveletPartial n z‖ < ε

  /-- The candidate locally uniform limit. -/
  waveletLimit : ℂ → ℂ

  /-- Full reconstruction equals the Cayley pullback of completed xi. -/
  reconstruction_eq_xi_cayley :
    ∀ z : ℂ,
      waveletLimit z = Ξ.xi (cayleyInv z)

  /-- Final Hurwitz-ready convergence statement to be proved by a concrete model. -/
  locallyUniformRenormalizedLimit :
    TendstoLocallyUniformly waveletPartial waveletLimit Filter.atTop

/--
Bridge from the Laplace--Mellin realization to the discrete Hurwitz--Clifford
cascade socket.
-/
@[rep_depth operator]
def toPrimeHurwitzCliffordCascadeRealization
    {F : ParaunitaryCliffordFilterBank}
    {A : PrimeLeeYangApproximants}
    {Ξ : CompletedXiFunction}
    (R : PrimeHurwitzWaveletXiRealization F A Ξ) :
    PrimeHurwitzCliffordCascadeRealization F R.cascade A Ξ where
  cascadePartial := R.waveletPartial
  partial_eq_renormZ := R.partial_eq_renormZ
  holomorphicPartials := R.holomorphicPartials
  locallyUniformBounded := R.locallyUniformBounded
  compactUniformTailControl := R.compactUniformTailControl
  cascadeLimit := R.waveletLimit
  reconstruction_eq_xi_cayley := R.reconstruction_eq_xi_cayley
  locallyUniformRenormalizedLimit := R.locallyUniformRenormalizedLimit

end InfoGeometry.Canonical.PrimeLaplaceMellinHurwitzWaveletLimit
