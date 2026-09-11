import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BayesianMarkovChain
import InfoGeometry.Canonical.BayesianHodgeCurrent
import InfoGeometry.Topology.DiscreteHodgeStabilizer

/-!
# Bayesian Markov / Discrete Dirac--Hodge Bridge

Theorem-safe adapter between the Bayesian projection/Markov socket and the
finite discrete Hodge stabilizer layer.

No analytic convergence, CP construction, graph limit, or continuum spacetime
claim is asserted here.  The bridge only transports explicit Bayesian-minimizer
certificates into the finite exact/coexact/harmonic Hodge sectors.
-/

namespace InfoGeometry.Topology.BayesianDiracHodgeBridge

open InfoGeometry.Canonical.BayesianMarkovChain.TensorLimitStateSpace
open InfoGeometry.Topology.EckmannDiscreteHodge

noncomputable section

universe u

abbrev IsCodeState' {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (u : Fin n1 → ℝ) : Prop :=
  InfoGeometry.Canonical.BayesianHodgeCurrent.IsProtectedHarmonicCurrent d0 d1 u

abbrev IsExactError' {n0 n1 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (e : Fin n1 → ℝ) : Prop :=
  InfoGeometry.Canonical.BayesianHodgeCurrent.IsDetailedBalanceCurrent d0 e

abbrev IsCoexactError' {n1 n2 : ℕ}
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (c : Fin n1 → ℝ) : Prop :=
  InfoGeometry.Canonical.BayesianHodgeCurrent.IsEntropyLoopCurrent d1 c

/-- A Bayesian Markov step projected to a degree-one discrete Hodge current. -/
structure BayesianHodgeCurrentBridge
    (State : Type u)
    {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ) where
  prior : State
  posterior : State
  transition : State → State
  divergence : State → State → ℝ
  constraint : State → Prop
  current : State → Fin n1 → ℝ
  bayesProjection : IsBayesianProjection divergence constraint prior posterior
  transition_eq_posterior : transition prior = posterior

namespace BayesianHodgeCurrentBridge

variable {State : Type u} {n0 n1 n2 : ℕ}
variable {d0 : Matrix (Fin n1) (Fin n0) ℝ}
variable {d1 : Matrix (Fin n2) (Fin n1) ℝ}
variable (B : BayesianHodgeCurrentBridge State d0 d1)

/-- The Markov step is the supplied Bayesian projection. -/
theorem transition_is_bayesian_projection :
    IsBayesianProjection B.divergence B.constraint B.prior (B.transition B.prior) :=
  markov_step_is_bayesian_projection B.transition B.divergence B.constraint
    B.prior B.posterior B.transition_eq_posterior B.bayesProjection

/-- The posterior/current step lies in the local constraint submanifold. -/
theorem posterior_mem_constraint :
    B.constraint (B.transition B.prior) :=
  bayesian_projection_mem B.divergence B.constraint B.prior (B.transition B.prior)
    (transition_is_bayesian_projection B)

/-- The Markov/Bayesian posterior minimizes the supplied divergence. -/
theorem posterior_minimizes (candidate : State) (hc : B.constraint candidate) :
    B.divergence (B.transition B.prior) B.prior ≤ B.divergence candidate B.prior :=
  bayesian_projection_minimizes B.divergence B.constraint B.prior (B.transition B.prior)
    (transition_is_bayesian_projection B) candidate hc

/-- Harmonic posterior currents are orthogonal to exact local errors. -/
theorem harmonic_current_orthogonal_exact_error
    {e : Fin n1 → ℝ}
    (hh : IsCodeState' d0 d1 (B.current B.posterior))
    (he : IsExactError' d0 e) :
    eckmannDot (B.current B.posterior) e = 0 :=
  InfoGeometry.Topology.DiscreteHodgeStabilizer.harmonic_orthogonal_exact d0 d1 hh he

/-- Harmonic posterior currents are orthogonal to coexact local errors. -/
theorem harmonic_current_orthogonal_coexact_error
    {c : Fin n1 → ℝ}
    (hh : IsCodeState' d0 d1 (B.current B.posterior))
    (hc : IsCoexactError' d1 c) :
    eckmannDot (B.current B.posterior) c = 0 :=
  InfoGeometry.Topology.DiscreteHodgeStabilizer.harmonic_orthogonal_coexact d0 d1 hh hc

/-- Combined Hodge protection for a harmonic Bayesian posterior current. -/
theorem harmonic_current_hodge_protection
    {e c : Fin n1 → ℝ}
    (hh : IsCodeState' d0 d1 (B.current B.posterior))
    (he : IsExactError' d0 e)
    (hc : IsCoexactError' d1 c) :
    eckmannDot (B.current B.posterior) e = 0 ∧
      eckmannDot (B.current B.posterior) c = 0 :=
  InfoGeometry.Topology.DiscreteHodgeStabilizer.hodge_orthogonal_protection d0 d1 hh he hc

end BayesianHodgeCurrentBridge

/--
Compatibility name for an exact degree-one Hodge current.

Detailed balance and KMS stationarity require transition-rate and state data;
they do not follow from exactness alone and are not stored as free propositions.
-/
abbrev ExactDetailedBalanceSector
    {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (_d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (current : Fin n1 → ℝ) : Prop :=
  IsExactError' d0 current

/--
Coexact Hodge current sector.

Entropy production is derived below as the native squared Hodge norm; it is
not supplied as an independent scalar together with an equality certificate.
-/
abbrev CoexactEntropySector
    {n1 n2 : ℕ}
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (current : Fin n1 → ℝ) : Prop :=
  IsCoexactError' d1 current

namespace CoexactEntropySector

variable {n1 n2 : ℕ}
variable {d1 : Matrix (Fin n2) (Fin n1) ℝ}
variable {current : Fin n1 → ℝ}
variable (C : CoexactEntropySector d1 current)

/-- Entropy-production readout of a coexact current: its squared Hodge norm. -/
def entropyCurrent : ℝ :=
  eckmannDot current current

/-- The native coexact entropy-current readout is nonnegative. -/
theorem entropy_current_nonneg : 0 ≤ entropyCurrent (current := current) :=
  eckmannDot_self_nonneg current

end CoexactEntropySector

/-- Harmonic Hodge sector represented by the native harmonic-code predicate. -/
abbrev HarmonicTopologicalSector
    {n0 n1 n2 : ℕ}
    (d0 : Matrix (Fin n1) (Fin n0) ℝ)
    (d1 : Matrix (Fin n2) (Fin n1) ℝ)
    (current : Fin n1 → ℝ) : Prop :=
  IsCodeState' d0 d1 current

namespace HarmonicTopologicalSector

variable {n0 n1 n2 : ℕ}
variable {d0 : Matrix (Fin n1) (Fin n0) ℝ}
variable {d1 : Matrix (Fin n2) (Fin n1) ℝ}
variable {current : Fin n1 → ℝ}
variable (H : HarmonicTopologicalSector d0 d1 current)

/-- Harmonic currents are orthogonal to exact and coexact errors. -/
theorem protected_orthogonal_to_local_errors
    (H : HarmonicTopologicalSector d0 d1 current)
    {e c : Fin n1 → ℝ}
    (he : IsExactError' d0 e)
    (hc : IsCoexactError' d1 c) :
    eckmannDot current e = 0 ∧ eckmannDot current c = 0 := by
  exact
    ⟨InfoGeometry.Canonical.BayesianHodgeCurrent.protected_orthogonal_detailedBalance
        d0 d1 H he,
      InfoGeometry.Canonical.BayesianHodgeCurrent.protected_orthogonal_entropyLoop
        d0 d1 H hc⟩

end HarmonicTopologicalSector

end

end InfoGeometry.Topology.BayesianDiracHodgeBridge
