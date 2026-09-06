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
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Canonical.FormalPrimeRootSystem

open scoped BigOperators

/-!
## Finite readback capstone

The complex-valued fermionic polynomial and the real-valued formal-root
partition are deliberately kept as separate readouts.  The theorems below
only compose their native finite owners; they do not identify the carriers.
-/

theorem finite_fermionic_readback
    (P : PrimeRegister) (x : ℕ → ℂ) :
    finiteMobiusDirichletPolynomial P x =
      finiteFermionicEulerProduct P x := by
  exact finiteMobiusDirichletPolynomial_eq_finiteFermionicEulerProduct P x

theorem finite_primon_weyl_readback
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finitePrimonPartition L β =
      (evaluatedWeylDenominator L β)⁻¹ := by
  exact finitePrimonPartition_eq_evaluatedWeylDenominator_inv L β

/-!
When the two finite cutoffs are explicitly the same, the complex fermionic
readout is the scalar extension of the real Weyl denominator.  This is a
readout equality with concrete hypotheses, not an identification of the
underlying state carriers.
-/
theorem finite_fermionic_eq_complex_weyl_denominator
    (P : PrimeRegister) (L : FormalPrimeRootLattice)
    (hprimes : P.primes = L.primes)
    (x : ℕ → ℂ) (r : ℕ → ℝ)
    (hx : ∀ p, x p = (r p : ℂ)) :
    finiteFermionicEulerProduct P x =
      (weylDenominatorProduct L r : ℂ) := by
  unfold finiteFermionicEulerProduct weylDenominatorProduct
  rw [hprimes]
  simp [rootThermalVariable, hx]

/-!
The two readbacks form the finite operatorial/arithmetic corridor.  The
conjunction is a packaging theorem, not an equivalence between the complex
fermionic and real Weyl carriers.
-/
theorem finite_operatorial_log_potential_readback
    (P : PrimeRegister) (x : ℕ → ℂ)
    (L : FormalPrimeRootLattice) (β : ℝ) :
    finiteMobiusDirichletPolynomial P x =
        finiteFermionicEulerProduct P x ∧
      finitePrimonPartition L β =
        (evaluatedWeylDenominator L β)⁻¹ := by
  exact ⟨finite_fermionic_readback P x,
    finite_primon_weyl_readback L β⟩

end InfoGeometry.Canonical.SouriauOperatorialLogPotentialFiniteReadback
