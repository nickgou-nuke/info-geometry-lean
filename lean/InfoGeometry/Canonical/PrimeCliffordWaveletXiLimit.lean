import Mathlib.Tactic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import InfoGeometry.Meta.Architecture
import InfoGeometry.Analysis.CliffordWaveletTransform

/-!
# InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit

Prime-specific Clifford wavelet limit socket.

This file connects the Clifford-wavelet reconstruction machinery to the
renormalized prime Lee--Yang approximants.

It does not prove RH.  It formulates the exact Hestenes--Krein/filtered-colimit
wavelet theorem that would replace the raw Hurwitz-style convergence property.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit

open InfoGeometry.Analysis.CliffordWaveletTransform

/-- Cayley inverse used in the RH/Lee--Yang bridge. -/
@[rep_depth operator]
def cayleyInv (z : ℂ) : ℂ :=
  z / (1 + z)

/-- Abstract completed-`xi` function.

The concrete owner should later replace this by the completed Riemann `xi`
function.
-/
@[rep_depth operator]
abbrev CompletedXiFunction :=
  {xi : ℂ → ℂ // ∃ s, xi s ≠ 0}

namespace CompletedXiFunction

abbrev xi (X : CompletedXiFunction) : ℂ → ℂ := X.1
abbrev nontrivial (X : CompletedXiFunction) : ∃ s, X.xi s ≠ 0 := X.2

end CompletedXiFunction

/-- Prime Lee--Yang approximants with nonvanishing renormalization. -/
@[rep_depth operator]
structure PrimeLeeYangApproximants where
  Z : ℕ → ℂ → ℂ
  R : ℕ → ℂ → ℂ
  renorm_nonzero : ∀ N z, R N z ≠ 0

/-- Renormalized approximant. -/
@[rep_depth operator]
def PrimeLeeYangApproximants.renormZ
    (A : PrimeLeeYangApproximants) (N : ℕ) (z : ℂ) : ℂ :=
  A.R N z * A.Z N z

/-- Clifford wavelet realization of the prime approximants.

This is the new Hestenes--Krein/colimit bridge: the prime approximants are not
arbitrary functions; they are finite Clifford-wavelet reconstructions / partial
sums.
-/
@[rep_depth operator]
structure PrimeCliffordWaveletRealization
    (W : CliffordWaveletModel)
    (A : PrimeLeeYangApproximants)
    (Xi : CompletedXiFunction) where

  /-- The prime signal reconstructed by the Clifford wavelet transform. -/
  primeSignal : W.Signal

  /-- Finite wavelet partial sum / cutoff readout. -/
  waveletPartial : ℕ → ℂ → ℂ

  /-- The finite wavelet partial sums match the renormalized approximants. -/
  partial_eq_renormZ :
    ∀ N z, waveletPartial N z = A.renormZ N z

  /-- Each finite wavelet partial is complex differentiable. -/
  holomorphicPartials :
    ∀ N, Differentiable ℂ (waveletPartial N)

  /-- The finite partials are uniformly bounded on compact subsets. -/
  locallyUniformBounded :
    ∀ K : Set ℂ, IsCompact K →
      ∃ C : ℝ, ∀ N z, z ∈ K → ‖waveletPartial N z‖ ≤ C

  /-- The partials are Cauchy uniformly on every compact subset. -/
  compactUniformTailControl :
    ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ N₀, ∀ m n, N₀ ≤ m → N₀ ≤ n →
        ∀ z, z ∈ K → ‖waveletPartial m z - waveletPartial n z‖ < ε

  /-- The candidate locally uniform limit. -/
  waveletLimit : ℂ → ℂ

  /-- Identification of the full wavelet reconstruction with completed `xi`. -/
  reconstruction_eq_xi_cayley :
    ∀ z : ℂ,
      waveletLimit z = Xi.xi (cayleyInv z)

  /-- The analytic conclusion needed by the Hurwitz bridge. -/
  locallyUniformRenormalizedLimit :
    TendstoLocallyUniformly waveletPartial waveletLimit Filter.atTop

/-- Extract the Hurwitz-ready convergence property from the Clifford wavelet
realization. -/
@[rep_depth operator]
def locallyUniformLimit_of_cliffordWaveletRealization
    (W : CliffordWaveletModel)
    (A : PrimeLeeYangApproximants)
    (Xi : CompletedXiFunction)
    (R : PrimeCliffordWaveletRealization W A Xi) :
    TendstoLocallyUniformly R.waveletPartial R.waveletLimit Filter.atTop :=
  R.locallyUniformRenormalizedLimit

end InfoGeometry.Canonical.PrimeCliffordWaveletXiLimit
