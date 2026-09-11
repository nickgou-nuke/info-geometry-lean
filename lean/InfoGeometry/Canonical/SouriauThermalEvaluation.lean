import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Algebraic.SplitSuperGeometry

/-!
# InfoGeometry.Canonical.SouriauThermalEvaluation

Thermal evaluation of the finite prime-root Weyl denominator.  The map is kept
finite and explicit: `e^{-α_p}` is sent to a supplied value `p^(-β)` (or, in a
more invariant implementation, to `exp(-⟨α_p, β⟩)`).
-/

namespace InfoGeometry.Canonical.SouriauThermalEvaluation

open scoped BigOperators
open FormalPrimeRootSystem

set_option linter.dupNamespace false in
/-- Souriau thermal evaluation rule for a finite prime cutoff. -/
@[rep_depth thermo]
structure SouriauThermalEvaluation (L : FormalPrimeRootLattice) where
  beta : ℝ
  /-- Souriau pairing of a prime root with the inverse-temperature element. -/
  rootPairing : ℕ → ℝ
  p_neg_beta : ℕ → ℝ
  e_neg_alpha : ℕ → ℝ
  /-- Prime-root pairing is the logarithmic prime energy weighted by `β`. -/
  pairing_eq_beta_log :
    ∀ p ∈ L.primes, rootPairing p = beta * Real.log (p : ℝ)
  /-- The evaluated formal root exponential is the exponential of the pairing. -/
  e_neg_alpha_eq_exp_neg_pairing :
    ∀ p ∈ L.primes, e_neg_alpha p = Real.exp (-rootPairing p)
  /-- The conventional prime thermal weight is `exp (-β log p)`. -/
  p_neg_beta_eq_exp_neg_beta_log :
    ∀ p ∈ L.primes, p_neg_beta p = Real.exp (-beta * Real.log (p : ℝ))
  e_neg_alpha_eq_p_neg_beta : ∀ p ∈ L.primes, e_neg_alpha p = p_neg_beta p

namespace SouriauThermalEvaluation

variable {L : FormalPrimeRootLattice}
variable (E : SouriauThermalEvaluation L)

/-- Native readback of the Souriau prime-root pairing. -/
@[rep_depth thermo]
theorem rootPairing_eq_beta_log
    (p : ℕ) (hp : p ∈ L.primes) :
    E.rootPairing p = E.beta * Real.log (p : ℝ) :=
  E.pairing_eq_beta_log p hp

/-- Thermal root evaluation is the exponential of the negative Souriau pairing. -/
@[rep_depth thermo]
theorem e_neg_alpha_eq_exp_neg_rootPairing
    (p : ℕ) (hp : p ∈ L.primes) :
    E.e_neg_alpha p = Real.exp (-E.rootPairing p) :=
  E.e_neg_alpha_eq_exp_neg_pairing p hp

/-- Prime thermal weight has the native Boltzmann logarithmic form. -/
@[rep_depth thermo]
theorem p_neg_beta_eq_boltzmannRootVariable
    (p : ℕ) (hp : p ∈ L.primes) :
    E.p_neg_beta p = boltzmannRootVariable E.beta p := by
  simpa [boltzmannRootVariable] using E.p_neg_beta_eq_exp_neg_beta_log p hp

end SouriauThermalEvaluation

/-- Product of evaluated prime factors on a subset. -/
@[rep_depth thermo]
def evaluatedPrimeMonomial {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, E.p_neg_beta p

/-- Finite evaluated Weyl/Euler product `∏_{p∈P}(1-p^{-β})`. -/
@[rep_depth thermo]
def finiteEvaluatedDenominator {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  ∏ p ∈ L.primes, (1 - E.p_neg_beta p)

/-- Finite evaluated alternating subset expansion. -/
@[rep_depth thermo]
def finiteEvaluatedAlternatingSum {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  ∑ S ∈ L.primes.powerset, ((-1 : ℝ) ^ S.card) * evaluatedPrimeMonomial E S

/--
Finite Euler/Weyl identity under Souriau thermal evaluation:
`∏_{p∈P}(1-p^{-β}) = ∑_{S⊆P} (-1)^{|S|}(∏_{p∈S}p)^{-β}`.
-/
@[rep_depth thermo]
theorem finite_euler_weyl_identity {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) :
    finiteEvaluatedDenominator E = finiteEvaluatedAlternatingSum E := by
  classical
  unfold finiteEvaluatedDenominator finiteEvaluatedAlternatingSum evaluatedPrimeMonomial
  simpa using (finite_prime_weyl_denominator L E.p_neg_beta)

/-- Legacy compatibility name for the individual thermal evaluation factor. -/
@[rep_depth thermo]
def rootThermalEvaluation {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) (p : ℕ) : ℝ :=
  E.e_neg_alpha p

/-- Legacy compatibility name for the finite parity product. -/
@[rep_depth thermo]
def finiteParityProduct {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  finiteEvaluatedDenominator E

/-- Legacy compatibility name for the finite parity alternating sum. -/
@[rep_depth thermo]
def finiteParitySubsetSum {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  finiteEvaluatedAlternatingSum E

/-- Compatibility alias for the finite parity/supertrace readout. -/
@[rep_depth thermo]
def splitFiniteParityTrace {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  finiteParityProduct E

/-- Compatibility alias for the finite parity alternating-sum readout. -/
@[rep_depth thermo]
def splitFiniteParitySupertrace {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  finiteParitySubsetSum E

end InfoGeometry.Canonical.SouriauThermalEvaluation
