import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Algebraic.SplitSuperGeometry

/-!
# InfoGeometry.Canonical.SouriauThermalEvaluation

Thermal evaluation of the finite prime-root Weyl denominator.  The map is kept
finite and explicit: `e^{-α_p}` is sent to a supplied value `p^(-β)` (or, in a
more invariant implementation, to `exp(-⟨α_p, β⟩)`).
-/

namespace SouriauThermalEvaluation

open scoped BigOperators
open InfoGeometry.Canonical.FormalPrimeRootSystem

set_option linter.dupNamespace false in
/-- Souriau thermal evaluation rule for a finite prime cutoff. -/
@[rep_depth thermo]
structure SouriauThermalEvaluation (L : FormalPrimeRootLattice) where
  beta : ℝ
  p_neg_beta : ℕ → ℝ
  e_neg_alpha : ℕ → ℝ
  e_neg_alpha_eq_p_neg_beta : ∀ p ∈ L.primes, e_neg_alpha p = p_neg_beta p
  pairing_eq_beta_log : Prop

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

end SouriauThermalEvaluation
