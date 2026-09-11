import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
