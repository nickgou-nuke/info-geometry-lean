import Mathlib
import InfoGeometry.Arithmetic.MobiusWittenWeylDenominator
import InfoGeometry.Canonical.WeylSignum

/-!
# Primon Supersymmetry

Finite theorem-owned core for the Möbius/Witten/Weyl primon dictionary.

#### BUCKET 1: CLOSED FINITE THEOREMS
`primon_susy_trace_preservation` proves trace preservation for a trace-free
chiral parity matrix under an involutive boundary twist.
`finite_primon_susy_master_identity` packages the finite Möbius polynomial,
finite Witten supertrace, finite Weyl denominator, and finite boson ×
denominator cancellation from the arithmetic owner.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The trace theorem requires explicit `M_parity * M_parity = 1` and
`trace Γ = 0`.  The finite cancellation theorem requires explicit nonzero local
Euler factors.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove the infinite identity `1 / ζ(s) = STr(e^{-sH})`,
McKean-Singer, Type II₁ traces, Klein-bottle global topology, Riemann-zero
localization, or the Riemann Hypothesis.
-/

noncomputable section

namespace PrimonSupersymmetry

open Matrix
open InfoGeometry.Arithmetic.PrimeBitWittenIndex

/--
Trace-free chiral parity matrices remain trace-free after an involutive Klein
boundary twist.
-/
theorem primon_susy_trace_preservation
    (Γ M_parity : Matrix (Fin 32) (Fin 32) ℝ)
    (h_twist : M_parity * M_parity = 1)
    (h_trace : Matrix.trace Γ = 0) :
    Matrix.trace (M_parity * Γ * M_parity) = 0 :=
  InfoGeometry.Canonical.WeylSignum.signum_trace_annihilation Γ M_parity h_twist h_trace

/--
Finite supersymmetric primon master identity.

This is a theorem-safe finite cutoff statement:

* Möbius polynomial = finite Weyl denominator;
* Möbius polynomial = finite Witten/fermionic supertrace;
* finite bosonic inverse denominator cancels the finite Möbius denominator.
-/
theorem finite_primon_susy_master_identity
    (P : PrimeRegister) (q : ℕ → ℂ)
    (h : ∀ p ∈ P.primes, (1 : ℂ) - q p ≠ 0) :
    InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial P q =
        InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeWeylDenominator P.primes q ∧
      InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial P q =
        InfoGeometry.Arithmetic.PrimonFinite.STrF P.primes q ∧
      InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeBosonicInverseDenominator
          P.primes q *
        InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial
          P q = 1 :=
  InfoGeometry.Arithmetic.MobiusWittenWeylDenominator.finite_mobius_witten_weyl_packet P q h

end PrimonSupersymmetry

