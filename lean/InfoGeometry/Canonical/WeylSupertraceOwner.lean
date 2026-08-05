import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.SouriauThermalEvaluation
import InfoGeometry.Canonical.ParityTraceWitness
import InfoGeometry.Canonical.PrimeGasPartitions
import InfoGeometry.Arithmetic.MobiusDirichletInverseBridge
import InfoGeometry.Arithmetic.PrimeSuperalgebra
import InfoGeometry.Algebraic.SplitSuperGeometry

/-!
# Weyl supertrace owner

Records the corrected prime/Weyl corridor: finite Weyl denominator equals the
finite parity supertrace, and the analytic limit is inverse zeta.  The bosonic
zeta trace and ordinary positive fermion trace remain separate.
-/

namespace InfoGeometry.Canonical.WeylSupertraceOwner

open InfoGeometry.Algebraic.SplitSignature

open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.SouriauThermalEvaluation
open InfoGeometry.Canonical.ParityTraceWitness
open InfoGeometry.Canonical.PrimeGasPartitions
open InfoGeometry.Arithmetic.PrimeSuperalgebra

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
    InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister :=
  ⟨W.lattice.primes, W.lattice.prime_mem⟩

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

/--
The infinite parity supertrace is the reciprocal of the bosonic prime product.
Unlike `InfiniteEulerProductWitness`, this is an actual complex-valued function.
-/
noncomputable def infiniteParitySupertrace (s : ℂ) : ℂ :=
  (infiniteComplexBosonicEulerProduct s)⁻¹

/-- The parity supertrace equals inverse zeta on the absolute-convergence half-plane. -/
theorem inverseZeta_is_paritySupertrace_limit
    {s : ℂ}
    (hs : 1 < s.re) :
    infiniteParitySupertrace s = (riemannZeta s)⁻¹ := by
  exact inverse_infiniteComplexBosonicEulerProduct_eq_inverse_riemannZeta hs

/-- The bosonic prime product is zeta on the absolute-convergence half-plane. -/
theorem zeta_is_bosonicTrace_limit
    {s : ℂ}
    (hs : 1 < s.re) :
    infiniteComplexBosonicEulerProduct s = riemannZeta s :=
  infiniteComplexBosonicEulerProduct_eq_riemannZeta hs

/--
The positive fermion channel is the genuine zeta ratio.  The second
half-plane condition follows from `1 < re s`.
-/
theorem fermionTrace_is_zeta_div_zeta_two_beta_limit
    {s : ℂ}
    (hs : 1 < s.re) :
    infiniteComplexPositiveFermionZetaRatio s =
      riemannZeta s / riemannZeta ((2 : ℂ) * s) := by
  apply infiniteComplexPositiveFermionZetaRatio_eq_zeta_div_zeta_two hs
  have htwo : (((2 : ℂ) * s).re) = 2 * s.re := by
    norm_num [Complex.mul_re]
  rw [htwo]
  linarith

/--
Split Clifford translation of the Weyl supertrace owner.

This keeps the prime/Weyl surface compatible with the new parity/supervolume
language without collapsing the prime lattice into the split Clifford carrier.
-/
abbrev SplitWeylSupertraceShadow (n : ℕ) := SplitCliffordEnd n

namespace SplitWeylSupertraceShadow

abbrev operator {n : ℕ} (S : SplitWeylSupertraceShadow n) : SplitCliffordEnd n := S

/-- The supertrace readout is derived from the supplied Clifford operator. -/
noncomputable def supertraceReadout
    {n : ℕ} (S : SplitWeylSupertraceShadow n) : ℝ :=
  cliffordSupertrace n S.operator

/-- The super-Berezinian readout is derived from the supplied Clifford operator. -/
noncomputable def superBerezinianReadout
    {n : ℕ} (S : SplitWeylSupertraceShadow n) : ℝ :=
  superBerezinian n S.operator

end SplitWeylSupertraceShadow



end InfoGeometry.Canonical.WeylSupertraceOwner
