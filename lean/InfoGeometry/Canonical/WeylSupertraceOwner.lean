import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.SouriauThermalEvaluation
import InfoGeometry.Canonical.ParityTraceWitness
import InfoGeometry.Canonical.PrimeGasPartitions

/-!
# Weyl supertrace owner

Records the corrected prime/Weyl corridor: finite Weyl denominator equals the
finite parity supertrace, and the analytic limit is inverse zeta.  The bosonic
zeta trace and ordinary positive fermion trace remain separate.
-/

namespace InfoGeometry.Canonical.WeylSupertraceOwner

open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.SouriauThermalEvaluation
open InfoGeometry.Canonical.ParityTraceWitness
open InfoGeometry.Canonical.PrimeGasPartitions

/-- Bundle of the finite A₁^P supertrace facts. -/
@[rep_depth thermo]
structure FiniteWeylSupertraceOwner where
  lattice : FormalPrimeRootLattice
  evaluation : SouriauThermalEvaluation lattice
  denominator_eq_paritySupertrace : Prop
  denominator_eq_mobiusDirichletPolynomial : Prop

/-- The finite Euler/Weyl identity is available from the thermal evaluation. -/
theorem finiteWeylDenominator_eq_finiteParitySupertrace
    (L : FormalPrimeRootLattice)
    (E : SouriauThermalEvaluation L) :
    finiteEvaluatedDenominator E = finiteEvaluatedAlternatingSum E :=
  finite_euler_weyl_identity E

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

end InfoGeometry.Canonical.WeylSupertraceOwner
