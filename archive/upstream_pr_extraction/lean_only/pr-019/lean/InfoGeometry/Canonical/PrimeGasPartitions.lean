import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Algebraic.SplitSuperGeometry

/-!
# InfoGeometry.Canonical.PrimeGasPartitions

The corrected prime-gas partition layer keeps three traces distinct:

* bosonic trace: reciprocal product, the finite precursor of `ζ(β)`;
* ordinary fermionic trace: positive square-free product, the finite precursor
  of `ζ(β)/ζ(2β)`;
* parity supertrace: alternating product, the finite Weyl-denominator analogue
  and finite precursor of `1/ζ(β)`.

Infinite Euler products are exposed only through explicit convergence/witness
packets.
-/

namespace InfoGeometry.Canonical.PrimeGasPartitions

open scoped BigOperators
open InfoGeometry.Canonical.FormalPrimeRootSystem

/-- Infinite Euler-product convergence witness with explicit zeta/parity channels. -/
@[rep_depth thermo]
structure InfiniteEulerProductConvergenceWitness where
  beta : ℝ
  halfPlane_Re_gt_one : Prop
  zeta : ℝ
  zeta_two_beta : ℝ
  inverseZeta : ℝ
  bosonTrace : ℝ
  fermionTrace : ℝ
  parityTrace : ℝ
  boson_eq_zeta : bosonTrace = zeta
  fermion_eq_zeta_div_zeta_two_beta : fermionTrace = zeta / zeta_two_beta
  parity_eq_inverse_zeta : parityTrace = inverseZeta

/-- Finite bosonic prime trace `∏_{p∈P}(1-p^{-β})^{-1}`. -/
@[rep_depth thermo]
noncomputable def finiteBosonTrace (L : FormalPrimeRootLattice) (p_neg_beta : ℕ → ℝ) : ℝ :=
  ∏ p ∈ L.primes, (1 - p_neg_beta p)⁻¹

/-- Finite ordinary fermion trace `∏_{p∈P}(1+p^{-β})`. -/
@[rep_depth thermo]
def finiteFermionTrace (L : FormalPrimeRootLattice) (p_neg_beta : ℕ → ℝ) : ℝ :=
  ∏ p ∈ L.primes, (1 + p_neg_beta p)

/-- Finite fermionic parity supertrace `∏_{p∈P}(1-p^{-β})`. -/
@[rep_depth thermo]
def finiteParityTrace (L : FormalPrimeRootLattice) (p_neg_beta : ℕ → ℝ) : ℝ :=
  ∏ p ∈ L.primes, (1 - p_neg_beta p)

/--
Analytic/infinite Euler-product witness.  This is intentionally separate from
finite products: convergence in the usual half-plane must be supplied here.
-/
@[rep_depth thermo]
structure InfiniteEulerProductWitness where
  beta : ℝ
  halfPlane_Re_gt_one : Prop
  zeta : ℝ
  zeta_two_beta : ℝ
  inverseZeta : ℝ
  bosonTrace : ℝ
  fermionTrace : ℝ
  parityTrace : ℝ
  boson_eq_zeta : bosonTrace = zeta
  fermion_eq_zeta_div_zeta_two_beta : fermionTrace = zeta / zeta_two_beta
  parity_eq_inverse_zeta : parityTrace = inverseZeta

@[rep_depth thermo]
theorem bosonTrace_eq_zeta (W : InfiniteEulerProductWitness) :
    W.bosonTrace = W.zeta :=
  W.boson_eq_zeta

@[rep_depth thermo]
theorem fermionTrace_eq_zeta_div_zeta_two_beta (W : InfiniteEulerProductWitness) :
    W.fermionTrace = W.zeta / W.zeta_two_beta :=
  W.fermion_eq_zeta_div_zeta_two_beta

@[rep_depth thermo]
theorem parityTrace_eq_inverse_zeta (W : InfiniteEulerProductWitness) :
    W.parityTrace = W.inverseZeta :=
  W.parity_eq_inverse_zeta

/--
Compatibility shadow for the prime-side parity supertrace.

This keeps the old finite/infinite prime-gas vocabulary intact while exposing
the new supergeometry naming.
-/
structure SplitPrimeSupertraceShadow where
  parityTrace : ℝ
  supertraceReadout : ℝ
  parityTrace_eq_supertraceReadout : parityTrace = supertraceReadout

namespace SplitPrimeSupertraceShadow

@[simp]
theorem parityTrace_eq_supertrace
    (S : SplitPrimeSupertraceShadow) :
    S.parityTrace = S.supertraceReadout :=
  S.parityTrace_eq_supertraceReadout

end SplitPrimeSupertraceShadow

end InfoGeometry.Canonical.PrimeGasPartitions
