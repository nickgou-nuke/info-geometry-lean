import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Basic
import InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge

/-!
# InfoGeometry.Arithmetic.ArithmeticErlangenSquareRootBridge

Finite square-root / Pfaffian / Erlangen bridge for prime-gas readouts.

This module formalizes only the conservative algebraic core:

* probability weights can be supplied as squares of amplitude weights;
* finite products of probability weights are squares of finite amplitude
  products;
* Pfaffian and supercharge interpretations are property gates.

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

lemma finiteAmplitudeProduct_nonneg
    {α : Type*} (A : Finset α) (amp : α → ℝ)
    (hamp : ∀ a ∈ A, 0 ≤ amp a) :
    0 ≤ finiteAmplitudeProduct A amp := by
  unfold finiteAmplitudeProduct
  exact Finset.prod_nonneg (fun a ha => hamp a ha)

lemma finiteAmplitudeProduct_pos
    {α : Type*} (A : Finset α) (amp : α → ℝ)
    (hamp : ∀ a ∈ A, 0 < amp a) :
    0 < finiteAmplitudeProduct A amp := by
  unfold finiteAmplitudeProduct
  exact Finset.prod_pos hamp

lemma finiteAmplitudeProduct_ne_zero
    {α : Type*} (A : Finset α) (amp : α → ℝ)
    (hamp : ∀ a ∈ A, amp a ≠ 0) :
    finiteAmplitudeProduct A amp ≠ 0 := by
  unfold finiteAmplitudeProduct
  exact Finset.prod_ne_zero_iff.mpr hamp

/--
Finite product of probability weights.

In the primon reading, a local probability/Gibbs weight is `p^{-β}`.
-/
def finiteProbabilityProduct
    {α R : Type*} [CommMonoid R]
    (A : Finset α)
    (prob : α → R) : R :=
  ∏ a ∈ A, prob a

lemma finiteProbabilityProduct_nonneg
    {α : Type*} (A : Finset α) (prob : α → ℝ)
    (hprob : ∀ a ∈ A, 0 ≤ prob a) :
    0 ≤ finiteProbabilityProduct A prob := by
  unfold finiteProbabilityProduct
  exact Finset.prod_nonneg (fun a ha => hprob a ha)

lemma finiteProbabilityProduct_pos
    {α : Type*} (A : Finset α) (prob : α → ℝ)
    (hprob : ∀ a ∈ A, 0 < prob a) :
    0 < finiteProbabilityProduct A prob := by
  unfold finiteProbabilityProduct
  exact Finset.prod_pos hprob

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
structure FiniteAmplitudeSquareRootData
    (α R : Type*) [CommMonoid R] where
  support : Finset α
  amplitude : α → R
  probability : α → R
  local_square :
    ∀ a ∈ support, probability a = amplitude a ^ 2

namespace FiniteAmplitudeSquareRootData

variable
    {α R : Type*} [CommMonoid R]
    (P : FiniteAmplitudeSquareRootData α R)

/-- Product-level square-root law for the packet. -/
theorem probabilityProduct_eq_amplitudeProduct_sq :
    finiteProbabilityProduct P.support P.probability =
      finiteAmplitudeProduct P.support P.amplitude ^ 2 :=
  finiteProbabilityProduct_eq_amplitudeProduct_sq
    P.support P.amplitude P.probability P.local_square

end FiniteAmplitudeSquareRootData



end InfoGeometry.Arithmetic.ArithmeticErlangenSquareRootBridge
