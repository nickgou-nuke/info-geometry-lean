import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.SouriauThermalEvaluation
import InfoGeometry.Canonical.ParityTraceWitness
import InfoGeometry.Canonical.PrimeGasPartitions
import InfoGeometry.Arithmetic.MobiusDirichletInverseBridge
import InfoGeometry.Algebraic.SplitSuperGeometry

/-!
# Weyl supertrace owner

Records the corrected prime/Weyl corridor: finite Weyl denominator equals the
finite parity supertrace, and the analytic limit is inverse zeta.  The bosonic
zeta trace and ordinary positive fermion trace remain separate.
-/

namespace WeylSupertraceOwner

open InfoGeometry.Algebraic.SplitSignature

open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.SouriauThermalEvaluation
open InfoGeometry.Canonical.ParityTraceWitness
open InfoGeometry.Canonical.PrimeGasPartitions

/-- Bundle of the finite A₁^P supertrace facts. -/
@[rep_depth thermo]
structure FiniteWeylSupertraceOwner where
  lattice : FormalPrimeRootLattice
  evaluation : SouriauThermalEvaluation lattice

/-- The finite Euler/Weyl identity is available from the thermal evaluation. -/
theorem finiteWeylDenominator_eq_finiteParitySupertrace
    (L : FormalPrimeRootLattice)
    (E : SouriauThermalEvaluation L) :
    finiteEvaluatedDenominator E = finiteEvaluatedAlternatingSum E :=
  finite_euler_weyl_identity E

/-- A finite Weyl supertrace packet reads back the finite denominator/parity equality. -/
theorem finiteWeylSupertraceOwner_denominator_eq_paritySupertrace
    (W : FiniteWeylSupertraceOwner) :
    finiteEvaluatedDenominator W.evaluation = finiteEvaluatedAlternatingSum W.evaluation :=
  finiteWeylDenominator_eq_finiteParitySupertrace W.lattice W.evaluation

/-- The finite Weyl packet can be reinterpreted as a prime register for the finite Möbius/Euler corridor. -/
def toPrimeRegister (W : FiniteWeylSupertraceOwner) :
    InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister where
  primes := W.lattice.primes
  prime_mem := W.lattice.prime_mem

/-- The finite Weyl packet also reads through the finite Möbius Dirichlet / fermionic Euler equality. -/
theorem finiteWeylSupertraceOwner_mobiusDirichlet_eq_finiteFermionicEulerProduct
    (W : FiniteWeylSupertraceOwner) :
    InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial
        (toPrimeRegister W) (fun p => (W.evaluation.e_neg_alpha p : ℂ)) =
      InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteFermionicEulerProduct
        (toPrimeRegister W) (fun p => (W.evaluation.e_neg_alpha p : ℂ)) := by
  exact _root_.InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial_eq_finiteFermionicEulerProduct
      (P := toPrimeRegister W) (x := fun p => (W.evaluation.e_neg_alpha p : ℂ))

/-- The finite Weyl packet reads out both finite finite-corridor equalities. -/
theorem finiteWeylSupertraceOwner_readback_corridor
    (W : FiniteWeylSupertraceOwner) :
    finiteEvaluatedDenominator W.evaluation = finiteEvaluatedAlternatingSum W.evaluation ∧
    InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial
        (toPrimeRegister W) (fun p => (W.evaluation.e_neg_alpha p : ℂ)) =
      InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteFermionicEulerProduct
        (toPrimeRegister W) (fun p => (W.evaluation.e_neg_alpha p : ℂ)) := by
  refine ⟨finiteWeylSupertraceOwner_denominator_eq_paritySupertrace W, ?_⟩
  exact finiteWeylSupertraceOwner_mobiusDirichlet_eq_finiteFermionicEulerProduct W

/-- Analytic infinite-product claims remain behind the PrimeGasPartitions witness. -/
theorem inverseZeta_is_paritySupertrace_limit
    (W : InfiniteEulerProductWitness) :
    W.parityTrace = W.inverseZeta :=
  W.parity_eq_inverse_zeta

/-- Bosonic zeta is explicitly the reciprocal/inverse-denominator trace, not the Weyl denominator. -/
theorem zeta_is_bosonicTrace_limit
    (W : InfiniteEulerProductWitness) :
    W.bosonTrace = W.zeta :=
  W.boson_eq_zeta

/-- Ordinary positive fermion trace remains separate from parity supertrace. -/
theorem fermionTrace_is_zeta_div_zeta_two_beta_limit
    (W : InfiniteEulerProductWitness) :
    W.fermionTrace = W.zeta / W.zeta_two_beta :=
  W.fermion_eq_zeta_div_zeta_two_beta

/--
Split Clifford translation of the Weyl supertrace owner.

This keeps the prime/Weyl surface compatible with the new parity/supervolume
language without collapsing the prime lattice into the split Clifford carrier.
-/
structure SplitWeylSupertraceShadow (n : ℕ) where
  operator : SplitCliffordEnd n := parityOp n
  supertraceReadout : ℝ := cliffordSupertrace n operator
  superBerezinianReadout : ℝ := superBerezinian n operator



end WeylSupertraceOwner
