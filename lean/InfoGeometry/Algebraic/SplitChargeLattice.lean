/-
InfoGeometry/Algebraic/SplitChargeLattice.lean

Integral charge lattice for the split/Narain carrier.

No complex imports.
No manifold coordinates.
No normalized states.

The primitive charge is an element of `Λ ⊕ Λ*`, written here as
momentum/winding data.
-/

import Mathlib.Data.Int.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Algebraic.SplitQuadraticForm

noncomputable section

namespace InfoGeometry.Algebraic.Split

open scoped BigOperators
open InfoGeometry.Algebraic.SplitSignature

/--
The integral split charge lattice.

`momentum` and `winding` are the two isotropic charge sectors.
In Narain language this is `Λ ⊕ Λ*`.
-/
abbrev SplitCharge (n : ℕ) : Type :=
  (Fin n → ℤ) × (Fin n → ℤ)

namespace SplitCharge

/-- Momentum component. -/
def momentum {n : ℕ} (q : SplitCharge n) : Fin n → ℤ :=
  q.1

/-- Winding / dual component. -/
def winding {n : ℕ} (q : SplitCharge n) : Fin n → ℤ :=
  q.2

/--
The hyperbolic pairing on the split charge lattice.

`⟪(m,w),(m',w')⟫ = m·w' + w·m'`.
-/
def hyperbolicPair {n : ℕ}
    (q r : SplitCharge n) : ℤ :=
  ∑ i : Fin n,
    (q.momentum i * r.winding i +
      q.winding i * r.momentum i)

/--
The integer quadratic norm associated to the hyperbolic lattice.

This is the even self-pairing convention:

`norm(q) = ⟪q,q⟫ = 2 m·w`.
-/
def hyperbolicNorm {n : ℕ}
    (q : SplitCharge n) : ℤ :=
  hyperbolicPair q q

/--
Realification of a split charge into the diagonal real split space.

This is only a real readout. The primitive integral lattice is still the
hyperbolic charge lattice above.
-/
def toDiagonalSplitSpace {n : ℕ}
    (q : SplitCharge n) : SplitModule n := fun i =>
  match i with
  | Sum.inl j => ((q.momentum j + q.winding j : ℤ) : ℝ)
  | Sum.inr j => ((q.momentum j - q.winding j : ℤ) : ℝ)

/--
A charge functional is a real-valued weight on the split charge lattice.

Later specializations:
* Cartan weights;
* number operators;
* momentum/winding energy;
* Jordan determinant weights;
* logarithmic Jacobian charges.
-/
abbrev ChargeFunctional (n : ℕ) := SplitCharge n → ℝ

namespace ChargeFunctional

/-- Compatibility projection for the former named weight field. -/
abbrev weight {n : ℕ} (E : ChargeFunctional n) : SplitCharge n → ℝ := E

end ChargeFunctional

/--
A finite charged spectrum.

This is the correct input for finite supertraces, finite Berezinians,
and finite zeta/supervolume products.
-/
structure FiniteChargeSpectrum (n : ℕ) where
  State : Type
  fintypeState : Fintype State
  decidableEqState : DecidableEq State
  charge : State → SplitCharge n
  parity : State → ℤ

attribute [instance] FiniteChargeSpectrum.fintypeState
attribute [instance] FiniteChargeSpectrum.decidableEqState

/--
Finite charge supertrace with respect to a charge functional.

This is the split-lattice version of the finite prime supertrace.
-/
def finiteChargeSupertrace {n : ℕ}
    (S : FiniteChargeSpectrum n)
    (E : ChargeFunctional n)
    (τ : ℝ) : ℝ :=
  ∑ s : S.State,
    ((S.parity s : ℤ) : ℝ) *
      Real.exp (-(τ * E.weight (S.charge s)))

end SplitCharge

end InfoGeometry.Algebraic.Split
