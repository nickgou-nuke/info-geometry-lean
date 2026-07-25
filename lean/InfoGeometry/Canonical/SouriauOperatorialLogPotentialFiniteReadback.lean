import Mathlib.Tactic
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Arithmetic.MobiusDirichletInverseBridge
import InfoGeometry.Arithmetic.KudinoorWittenIndexBridge
import InfoGeometry.Canonical.FormalPrimeRootSystem

/-!
# InfoGeometry.Canonical.SouriauOperatorialLogPotentialFiniteReadback

This file is a clean finite readback companion for
`InfoGeometry.Canonical.SouriauOperatorialLogPotential`.

It does not strengthen the tracked owner file to an infinite analytic theorem.
Instead it packages the already-proved finite owner corridor that honestly backs
its arithmetic/thermodynamic interpretation surface:

* finite Möbius Dirichlet polynomial = finite fermionic Euler product;
* finite weighted supertrace = finite Witten index under explicit pairing and
  zero-weight hypotheses;
* finite primon partition = inverse evaluated finite Weyl denominator.

No infinite Dirichlet series, no McKean-Singer heat-kernel theorem, and no
unconditional `1 / ζ(s) = STr(exp(-sH))` theorem are claimed here.
-/

namespace InfoGeometry.Canonical.SouriauOperatorialLogPotentialFiniteReadback

open InfoGeometry.Arithmetic.MobiusDirichletInverseBridge
open InfoGeometry.Arithmetic.KudinoorWittenIndexBridge
open InfoGeometry.Canonical.FormalPrimeRootSystem

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

@[rep_depth thermo]
theorem finiteMobiusDirichletPolynomial_eq_finiteFermionicEulerProduct
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (x : ℕ → ℂ) :
    finiteMobiusDirichletPolynomial P x =
      finiteFermionicEulerProduct P x :=
  _root_.InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial_eq_finiteFermionicEulerProduct P x

@[rep_depth thermo]
theorem finiteWeightedSupertrace_eq_finiteWittenIndex
    {ι : Type*} [DecidableEq ι]
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) (weight : ι → Int)
    (hzero : ∀ i ∈ levels, zero i → weight i = 1)
    (hpair : ∀ i ∈ levels, ¬ zero i → boson i = fermion i) :
    finiteWeightedSupertrace levels boson fermion weight =
      finiteWittenIndex levels zero boson fermion :=
  _root_.InfoGeometry.Arithmetic.KudinoorWittenIndexBridge.finiteWeightedSupertrace_eq_finiteWittenIndex
      levels zero boson fermion weight hzero hpair

@[rep_depth thermo]
theorem finitePrimonPartition_eq_evaluatedWeylDenominator_inv
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finitePrimonPartition L β = (evaluatedWeylDenominator L β)⁻¹ :=
  _root_.InfoGeometry.Canonical.FormalPrimeRootSystem.finitePrimonPartition_eq_evaluatedWeylDenominator_inv L β

@[rep_depth thermo]
theorem finite_readback_corridor
    {ι : Type*} [DecidableEq ι]
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (x : ℕ → ℂ)
    (levels : Finset ι) (zero : ι → Prop) [DecidablePred zero]
    (boson fermion : ι → Nat) (weight : ι → Int)
    (hzero : ∀ i ∈ levels, zero i → weight i = 1)
    (hpair : ∀ i ∈ levels, ¬ zero i → boson i = fermion i)
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finiteMobiusDirichletPolynomial P x =
      finiteFermionicEulerProduct P x ∧
    finiteWeightedSupertrace levels boson fermion weight =
      finiteWittenIndex levels zero boson fermion ∧
    finitePrimonPartition L β = (evaluatedWeylDenominator L β)⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · exact finiteMobiusDirichletPolynomial_eq_finiteFermionicEulerProduct P x
  · exact finiteWeightedSupertrace_eq_finiteWittenIndex
      levels zero boson fermion weight hzero hpair
  · exact finitePrimonPartition_eq_evaluatedWeylDenominator_inv L β

end InfoGeometry.Canonical.SouriauOperatorialLogPotentialFiniteReadback
