import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge
import InfoGeometry.Arithmetic.RHQuantumStabilityBridge

/-!
# InfoGeometry.Arithmetic.ArithmeticErlangenSquareRootBridge

Finite square-root / Pfaffian / Erlangen bridge for prime-gas readouts.

This module formalizes only the conservative algebraic core:

* probability weights can be supplied as squares of amplitude weights;
* finite products of probability weights are squares of finite amplitude
  products;
* Pfaffian and supercharge interpretations are witness gates.

No Riemann Hypothesis theorem, no zero-location theorem, no Super-Virasoro
construction, and no infinite Pfaffian/determinant theorem is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.ArithmeticErlangenSquareRootBridge

/-! ## 1. Finite amplitude square roots -/

/--
Finite product of amplitudes.

In the primon reading, a local amplitude is the square root of a Gibbs weight,
e.g. `p^{-β/2}`.
-/
def finiteAmplitudeProduct
    {α R : Type*} [CommMonoid R]
    (A : Finset α)
    (amp : α → R) : R :=
  ∏ a ∈ A, amp a

/--
Finite product of probability weights.

In the primon reading, a local probability/Gibbs weight is `p^{-β}`.
-/
def finiteProbabilityProduct
    {α R : Type*} [CommMonoid R]
    (A : Finset α)
    (prob : α → R) : R :=
  ∏ a ∈ A, prob a

/-- Square of a finite product equals the product of local squares. -/
theorem finiteAmplitudeProduct_sq
    {α R : Type*} [CommMonoid R]
    (A : Finset α)
    (amp : α → R) :
    finiteAmplitudeProduct A amp ^ 2 =
      ∏ a ∈ A, amp a ^ 2 := by
  unfold finiteAmplitudeProduct
  rw [pow_two, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro a ha
  rw [pow_two]

/--
If probability weights are local squares of amplitude weights, then the finite
probability product is the square of the finite amplitude product.
-/
theorem finiteProbabilityProduct_eq_amplitudeProduct_sq
    {α R : Type*} [CommMonoid R]
    (A : Finset α)
    (amp prob : α → R)
    (h : ∀ a ∈ A, prob a = amp a ^ 2) :
    finiteProbabilityProduct A prob =
      finiteAmplitudeProduct A amp ^ 2 := by
  unfold finiteProbabilityProduct
  rw [finiteAmplitudeProduct_sq]
  refine Finset.prod_congr rfl ?_
  intro a ha
  exact h a ha

/--
Amplitude/probability square-root packet.

This packages the finite version of `Ψ(n)^2 = ρ(n)`.
-/
structure FiniteAmplitudeSquareRootPacket
    (α R : Type*) [CommMonoid R] where
  support : Finset α
  amplitude : α → R
  probability : α → R
  local_square :
    ∀ a ∈ support, probability a = amplitude a ^ 2

namespace FiniteAmplitudeSquareRootPacket

variable
    {α R : Type*} [CommMonoid R]
    (P : FiniteAmplitudeSquareRootPacket α R)

/-- Product-level square-root law for the packet. -/
theorem probabilityProduct_eq_amplitudeProduct_sq :
    finiteProbabilityProduct P.support P.probability =
      finiteAmplitudeProduct P.support P.amplitude ^ 2 :=
  finiteProbabilityProduct_eq_amplitudeProduct_sq
    P.support P.amplitude P.probability P.local_square

end FiniteAmplitudeSquareRootPacket

/-! ## 2. Pfaffian and supercharge witness gates -/

/--
Pfaffian square-root gate.

For a concrete antisymmetric operator/matrix model, the owner module supplies
`pfaffian_sq_eq_determinant`.  This bridge does not construct a Pfaffian.
-/
structure PfaffianSquareRootGate
    (Carrier Scalar : Type*) [CommMonoid Scalar] where
  carrier : Carrier
  pfaffian : Scalar
  determinant : Scalar
  pfaffian_sq_eq_determinant :
    pfaffian ^ 2 = determinant

namespace PfaffianSquareRootGate

/-- Re-export of the supplied Pfaffian square law. -/
theorem square_law
    {Carrier Scalar : Type*} [CommMonoid Scalar]
    (P : PfaffianSquareRootGate Carrier Scalar) :
    P.pfaffian ^ 2 = P.determinant :=
  P.pfaffian_sq_eq_determinant

end PfaffianSquareRootGate

/--
Supercharge square-root gate.

The intended interpretation is `Q * Q = H`.  The concrete operator algebra and
domain questions are supplied by an owner module.
-/
structure SuperchargeSquareRootGate
    (Operator : Type*) [Mul Operator] where
  Q : Operator
  H : Operator
  square_law :
    Q * Q = H

namespace SuperchargeSquareRootGate

/-- Re-export of the supplied supercharge square law. -/
theorem valid
    {Operator : Type*} [Mul Operator]
    (S : SuperchargeSquareRootGate Operator) :
    S.Q * S.Q = S.H :=
  S.square_law

end SuperchargeSquareRootGate

/--
Arithmetic Erlangen square-root packet.

This records the square-root mechanisms without promoting them to an RH proof:

* amplitude squares give probability weights;
* Pfaffian squares give determinant readouts;
* supercharge squares give Hamiltonian readouts;
* RH or critical-line consequences remain in the supplied RH bridge.
-/
structure ArithmeticErlangenSquareRootPacket
    (α R Carrier Operator BRSTCharge StateSpace ZeroReadout WeylReadout
      ThetaReadout VacuumReadout : Type*)
    [CommMonoid R] [Mul Operator] where
  amplitude :
    FiniteAmplitudeSquareRootPacket α R
  pfaffian :
    PfaffianSquareRootGate Carrier R
  supercharge :
    SuperchargeSquareRootGate Operator
  rhBridge :
    InfoGeometry.Arithmetic.RHQuantumStabilityBridge.QuantumArithmeticRHBridge
      BRSTCharge StateSpace ZeroReadout WeylReadout
      ThetaReadout VacuumReadout

namespace ArithmeticErlangenSquareRootPacket

variable
    {α R Carrier Operator BRSTCharge StateSpace ZeroReadout WeylReadout
      ThetaReadout VacuumReadout : Type*}
    [CommMonoid R] [Mul Operator]

/-- The finite amplitude/probability square-root law in the bridge. -/
theorem amplitude_square_law
    (B : ArithmeticErlangenSquareRootPacket
      α R Carrier Operator BRSTCharge StateSpace ZeroReadout WeylReadout
      ThetaReadout VacuumReadout) :
    finiteProbabilityProduct B.amplitude.support B.amplitude.probability =
      finiteAmplitudeProduct B.amplitude.support B.amplitude.amplitude ^ 2 :=
  B.amplitude.probabilityProduct_eq_amplitudeProduct_sq

/-- The supplied Pfaffian square law in the bridge. -/
theorem pfaffian_square_law
    (B : ArithmeticErlangenSquareRootPacket
      α R Carrier Operator BRSTCharge StateSpace ZeroReadout WeylReadout
      ThetaReadout VacuumReadout) :
    B.pfaffian.pfaffian ^ 2 = B.pfaffian.determinant :=
  B.pfaffian.square_law

/-- The supplied supercharge square law in the bridge. -/
theorem supercharge_square_law
    (B : ArithmeticErlangenSquareRootPacket
      α R Carrier Operator BRSTCharge StateSpace ZeroReadout WeylReadout
      ThetaReadout VacuumReadout) :
    B.supercharge.Q * B.supercharge.Q = B.supercharge.H :=
  B.supercharge.valid

end ArithmeticErlangenSquareRootPacket

end InfoGeometry.Arithmetic.ArithmeticErlangenSquareRootBridge
