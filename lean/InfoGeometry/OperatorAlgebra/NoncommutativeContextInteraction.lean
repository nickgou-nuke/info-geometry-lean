/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import InfoGeometry.Core.PeirceDecomposition

/-!
# Contextual interactions in noncommutative operator algebras

The operator identities behind the transcript's density-matrix archetype are
stated for arbitrary associative rings with involution. Expectations are
represented by an additive cyclic functional, rather than by a chosen matrix
trace. No positivity, normalization, or probabilistic interpretation is
assumed without additional structure.
-/

namespace InfoGeometry.OperatorAlgebra.NoncommutativeContextInteraction

open InfoGeometry.Core.PeirceDecomposition

variable {A : Type*} [Ring A]

/-- The ordered product defect of two operators. -/
def commutator (a b : A) : A := a * b - b * a

/-- The symmetric product of two operators. -/
def anticommutator (a b : A) : A := a * b + b * a

/-- Lie action of an operator on the full operator algebra. -/
def innerLieAction (u x : A) : A := commutator u x

/-- Jordan action of an operator on the full operator algebra. -/
def innerJordanAction (u x : A) : A := anticommutator u x

/-- Symmetric two-branch operator channel with ordered left and right
amplitudes. -/
def crossSandwichChannel (u v x : A) : A := u * x * v + v * x * u

/-- Cyclicity converts the two-sided cross-sandwich channel into the pairing
with the Jordan mass operator. No condition on the observable or its relation
to an idempotent is needed. -/
theorem cyclicFunctional_crossSandwichChannel {S : Type*} [AddCommGroup S]
    (τ : A →+ S) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (u v x : A) :
    τ (crossSandwichChannel u v x) = τ ((u * v + v * u) * x) := by
  unfold crossSandwichChannel
  rw [map_add, hτ (u * x) v, hτ (v * x) u]
  calc
    τ (v * (u * x)) + τ (u * (v * x)) =
        τ ((v * u + u * v) * x) := by
          rw [← map_add]
          congr 1 <;> noncomm_ring
    _ = τ ((u * v + v * u) * x) := by
      congr 1
      noncomm_ring

/-- The exact mixed Lie--Jordan superoperator identities for two ordered
operators. The second identity retains its cross-sandwich defect; omitting
`2 • (u * x * v - v * x * u)` is not valid for arbitrary operators. -/
theorem mixed_boundary_superoperator_quartet (u v x : A) :
    innerJordanAction u (innerLieAction v x) +
        innerJordanAction v (innerLieAction u x) =
      commutator (u * v + v * u) x ∧
    innerLieAction u (innerJordanAction v x) -
        innerLieAction v (innerJordanAction u x) =
      anticommutator (commutator u v) x +
        2 • (u * x * v - v * x * u) ∧
    innerLieAction u (innerLieAction v x) -
        innerLieAction v (innerLieAction u x) =
      commutator (commutator u v) x ∧
    (innerJordanAction u (innerJordanAction v x) +
        innerJordanAction v (innerJordanAction u x)) +
      (innerLieAction u (innerLieAction v x) +
        innerLieAction v (innerLieAction u x)) =
      2 • anticommutator (u * v + v * u) x ∧
    (innerJordanAction u (innerJordanAction v x) +
        innerJordanAction v (innerJordanAction u x)) -
      (innerLieAction u (innerLieAction v x) +
        innerLieAction v (innerLieAction u x)) =
      4 • crossSandwichChannel u v x := by
  simp only [innerLieAction, innerJordanAction, commutator, anticommutator,
    crossSandwichChannel]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · noncomm_ring
  · noncomm_ring
  · noncomm_ring
  · noncomm_ring
  · noncomm_ring

/-- Ordered multiplication splits exactly into its symmetric and antisymmetric
operator parts. -/
theorem product_lie_jordan_split (a b : A) :
    2 • (a * b) = anticommutator a b + commutator a b := by
  simp only [two_nsmul, anticommutator, commutator]
  noncomm_ring

/-- A two-cycle of inner-commutator actions converts product conservation
into operator square and anticommutator identities. This is valid in every
associative operator ring, with no matrix coordinates or commutativity
assumptions. -/
theorem commutator_two_cycle_product_identities {p j e : A}
    (hFaraday : commutator p j = e) (hAmpere : commutator p e = j) :
    commutator p (j * e) = e * e + j * j ∧
    commutator p (e * e) = anticommutator j e ∧
    commutator p (j * j) = anticommutator e j ∧
    (commutator p (j * e) = 0 ↔ e * e + j * j = 0) ∧
    (commutator p (e * e) = 0 ↔ anticommutator j e = 0) := by
  have hFaraday' : p * j - j * p = e := by simpa [commutator] using hFaraday
  have hAmpere' : p * e - e * p = j := by simpa [commutator] using hAmpere
  have hJE : commutator p (j * e) = e * e + j * j := by
    change p * (j * e) - (j * e) * p = _
    calc
      _ = (p * j - j * p) * e + j * (p * e - e * p) := by noncomm_ring
      _ = e * e + j * j := by rw [hFaraday', hAmpere']
  have hEE : commutator p (e * e) = anticommutator j e := by
    change p * (e * e) - (e * e) * p = j * e + e * j
    calc
      _ = (p * e - e * p) * e + e * (p * e - e * p) := by noncomm_ring
      _ = j * e + e * j := by rw [hAmpere']
  have hJJ : commutator p (j * j) = anticommutator e j := by
    change p * (j * j) - (j * j) * p = e * j + j * e
    calc
      _ = (p * j - j * p) * j + j * (p * j - j * p) := by noncomm_ring
      _ = e * j + j * e := by rw [hFaraday']
  refine ⟨hJE, hEE, hJJ, ?_, ?_⟩
  · rw [hJE]
  · rw [hEE]

section Star

variable [StarRing A]

/-- The involution reverses the order of the operator commutator. -/
theorem star_commutator (a b : A) :
    star (commutator a b) = commutator (star b) (star a) := by
  simp only [commutator, star_sub, star_mul]

/-- The involution reverses the order of the symmetric operator product. -/
theorem star_anticommutator (a b : A) :
    star (anticommutator a b) = anticommutator (star b) (star a) := by
  simp only [anticommutator, star_add, star_mul]

/-- A single-branch contextual update by an operator and its adjoint. -/
def contextualDress (w x : A) : A := w * x * star w

/-- Adjoint dressing preserves self-adjointness in an arbitrary star ring. -/
theorem contextualDress_selfAdjoint {x : A} (hx : star x = x) (w : A) :
    star (contextualDress w x) = contextualDress w x := by
  simp only [contextualDress, star_mul, star_star, hx]
  rw [mul_assoc]

/-- For self-adjoint operators, the anticommutator is self-adjoint. -/
theorem anticommutator_selfAdjoint {a b : A}
    (ha : star a = a) (hb : star b = b) :
    star (anticommutator a b) = anticommutator a b := by
  simp only [anticommutator, star_add, star_mul, ha, hb]
  abel

/-- For self-adjoint operators, the commutator is skew-adjoint. -/
theorem commutator_skewAdjoint {a b : A}
    (ha : star a = a) (hb : star b = b) :
    star (commutator a b) = -commutator a b := by
  simp only [commutator, star_sub, star_mul, ha, hb]
  abel

end Star

/-- A cyclic additive functional on the operator algebra. -/
def IsCyclicFunctional {R : Type*} [AddCommGroup R] (τ : A →+ R) : Prop :=
  ∀ a b, τ (a * b) = τ (b * a)

/-- An algebraic density element relative to a chosen readout: it is
self-adjoint and has unit readout. Positivity is a separate hypothesis and is
not encoded by this predicate. -/
def IsUnitReadoutSelfAdjointElement {R : Type*} [Ring R] [StarRing A]
    (τ : A →+ R) (x : A) : Prop :=
  star x = x ∧ τ x = 1

/-- A cyclic functional forgets operator ordering inside a two-factor value. -/
theorem functional_commutator_zero {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ) (a b : A) :
    τ (commutator a b) = 0 := by
  simp only [commutator, map_sub]
  rw [hτ a b]
  exact sub_self _

/-- Every finite sum of inner-derivation fluxes has zero readout under a
cyclic additive functional.  This is the operator-algebraic divergence law;
it requires neither matrix coordinates nor commutation among the generators. -/
theorem cyclicFunctional_finite_innerDivergence_zero
    {R ι : Type*} [AddCommGroup R] [Fintype ι]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ)
    (H J : ι → A) :
    τ (∑ i, commutator (H i) (J i)) = 0 := by
  rw [map_sum]
  simp_rw [functional_commutator_zero τ hτ]
  simp

/-- Finite operator Laplacian generated by a family of inner derivations. -/
def finiteInnerCommutatorLaplacian {ι : Type*} [Fintype ι]
    (H : ι → A) (x : A) : A :=
  ∑ i, commutator (H i) (commutator (H i) x)

/-- Every finite inner-commutator Laplacian has zero cyclic readout. This is
the operator-valued divergence-of-gradient identity, with no matrix trace or
commutativity assumption on the generators. -/
theorem cyclicFunctional_finite_innerLaplacian_zero
    {R ι : Type*} [AddCommGroup R] [Fintype ι]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ)
    (H : ι → A) (x : A) :
    τ (finiteInnerCommutatorLaplacian H x) = 0 := by
  simpa [finiteInnerCommutatorLaplacian] using
    cyclicFunctional_finite_innerDivergence_zero τ hτ H
      (fun i => commutator (H i) x)

/-- The contextual expectation of a commutator is the cyclic pairing of the
context commutator with the second operator. -/
theorem contextual_commutator_cyclic_duality {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ) (p a b : A) :
    τ (p * commutator a b) = τ (commutator p a * b) := by
  have hcycle : τ (p * (b * a)) = τ ((a * p) * b) := by
    calc
      τ (p * (b * a)) = τ ((p * b) * a) := by rw [← mul_assoc]
      _ = τ (a * (p * b)) := hτ (p * b) a
      _ = τ ((a * p) * b) := by rw [← mul_assoc]
  calc
    τ (p * commutator a b) = τ (p * (a * b)) - τ (p * (b * a)) := by
      simp [commutator, map_sub, mul_sub]
    _ = τ ((p * a) * b) - τ ((a * p) * b) := by
      rw [← mul_assoc p a b, hcycle]
    _ = τ (commutator p a * b) := by
      simp [commutator, sub_mul, map_sub]

/-- The context commutator is exactly the difference of its two directed
Peirce transitions. Thus the contextual cyclic pairing reads the cross
correlation of the off-diagonal operator coherence against `b`. -/
theorem contextual_peirce_coherence_crosscorr {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ) {p a b : A} :
    τ (p * commutator a b) =
      τ ((component10 p a - component01 p a) * b) := by
  have hcoherence : commutator p a = component10 p a - component01 p a := by
    simp only [commutator, component10, component01, complementIdempotent]
    noncomm_ring
  rw [contextual_commutator_cyclic_duality τ hτ, hcoherence]

/-- If the first operator is pinched by the context, its contextual
commutator expectation vanishes for every second operator. -/
theorem contextual_commutator_zero_of_pinched {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ) {p a : A}
    (hpinched : commutator p a = 0) (b : A) :
    τ (p * commutator a b) = 0 := by
  rw [contextual_commutator_cyclic_duality τ hτ, hpinched, zero_mul, map_zero]

/-- A two-branch operator channel has the cyclic readout of its ordered mass
operator. No matrix trace, positivity, or commutation condition on `x` is
needed; cyclicity alone moves each outer factor around the functional. -/
theorem cyclicFunctional_cross_channel_readout {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ) (u v x : A) :
    τ (u * x * v + v * x * u) = τ ((v * u + u * v) * x) := by
  have hleft : τ (u * x * v) = τ ((v * u) * x) := by
    calc
      τ (u * x * v) = τ (v * (u * x)) := hτ (u * x) v
      _ = τ ((v * u) * x) := by rw [mul_assoc]
  have hright : τ (v * x * u) = τ ((u * v) * x) := by
    calc
      τ (v * x * u) = τ (u * (v * x)) := hτ (v * x) u
      _ = τ ((u * v) * x) := by rw [mul_assoc]
  calc
    τ (u * x * v + v * x * u) =
        τ ((v * u) * x) + τ ((u * v) * x) := by
      rw [map_add, hleft, hright]
    _ = τ ((v * u + u * v) * x) := by
      rw [add_mul, map_add]

/-- The antisymmetric two-branch channel has the cyclic readout of the
commutator mass, with the orientation sign fixed by the branch order. -/
theorem cyclicFunctional_cross_channel_skew_readout {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ) (u v x : A) :
    τ (u * x * v - v * x * u) = -τ ((u * v - v * u) * x) := by
  have hleft : τ (u * x * v) = τ ((v * u) * x) := by
    calc
      τ (u * x * v) = τ (v * (u * x)) := hτ (u * x) v
      _ = τ ((v * u) * x) := by rw [mul_assoc]
  have hright : τ (v * x * u) = τ ((u * v) * x) := by
    calc
      τ (v * x * u) = τ (u * (v * x)) := hτ (v * x) u
      _ = τ ((u * v) * x) := by rw [mul_assoc]
  calc
    τ (u * x * v - v * x * u) = τ ((v * u) * x) - τ ((u * v) * x) := by
      rw [map_sub, hleft, hright]
    _ = -τ ((u * v - v * u) * x) := by
      rw [sub_mul, map_sub]
      abel

/-- Cyclicity moves an adjoint-dressed operator through the expectation and
records its exact effect as the adjoint Gram sandwich `star w * w`. -/
theorem cyclic_contextualDress {R : Type*} [AddCommGroup R] [StarRing A]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ) (w x : A) :
    τ (contextualDress w x) = τ (x * star w * w) := by
  calc
    τ (contextualDress w x) = τ (w * (x * star w)) := by
      simp only [contextualDress, mul_assoc]
    _ = τ ((x * star w) * w) := hτ w (x * star w)

/-- Isometric adjoint dressing preserves every cyclic functional. -/
theorem contextualDress_cyclic_preserving_of_isometry {R : Type*}
    [AddCommGroup R] [StarRing A] (τ : A →+ R)
    (hτ : IsCyclicFunctional τ) (w x : A) (hw : star w * w = 1) :
    τ (contextualDress w x) = τ x := by
  rw [cyclic_contextualDress τ hτ, mul_assoc, hw, mul_one]

/-- Isometric adjoint dressing preserves self-adjointness and unit readout
for an algebraic density element, under an arbitrary cyclic functional. -/
theorem contextualDress_preserves_unitReadoutSelfAdjoint
    {R : Type*} [Ring R] [StarRing A] (τ : A →+ R)
    (hτ : IsCyclicFunctional τ) {x : A}
    (hx : IsUnitReadoutSelfAdjointElement τ x)
    (w : A) (hw : star w * w = 1) :
    IsUnitReadoutSelfAdjointElement τ (contextualDress w x) := by
  refine ⟨contextualDress_selfAdjoint hx.1 w, ?_⟩
  rw [contextualDress_cyclic_preserving_of_isometry τ hτ w x hw]
  exact hx.2

/-- A self-adjoint idempotent context turns adjoint dressing into the cyclic
projective affinity `τ(p * x)`, for any cyclic additive functional. -/
theorem cyclicFunctional_projectionDress_affinity {R : Type*}
    [AddCommGroup R] [StarRing A] (τ : A →+ R)
    (hτ : IsCyclicFunctional τ) {p x : A}
    (hp : p * p = p) (hps : star p = p) :
    τ (contextualDress p x) = τ (p * x) := by
  calc
    τ (contextualDress p x) = τ (x * star p * p) :=
      cyclic_contextualDress τ hτ p x
    _ = τ (x * p) := by rw [hps, mul_assoc, hp]
    _ = τ (p * x) := hτ x p

/-- A primal Lie--Jordan transport operator on the algebra. This is an
algebraic endomorphism formula and makes no manifold or differential claim. -/
def primalTransport (h s x : A) : A := commutator h x + anticommutator s x

/-- The dual transport reverses the sign of the Jordan part. -/
def dualTransport (h s x : A) : A := commutator h x - anticommutator s x

/-- The midpoint and skew parts of the primal/dual transports recover the
Lie and Jordan operator actions. These identities hold in an arbitrary
associative ring; they do not assume that either generator commutes with the
argument. -/
theorem primal_dual_midpoint_and_skew (h s x : A) :
    primalTransport h s x + dualTransport h s x = 2 • commutator h x ∧
    primalTransport h s x - dualTransport h s x = 2 • anticommutator s x := by
  constructor <;> simp only [primalTransport, dualTransport, two_nsmul,
    commutator, anticommutator] <;> noncomm_ring

/-- The Lie derivation acts on the Jordan product by the commutator with its
generator. This is the mixed Lie--Jordan identity in an operator algebra. -/
theorem commutator_anticommutator_exchange (h s x : A) :
    commutator h (anticommutator s x) -
      anticommutator s (commutator h x) =
        anticommutator (commutator h s) x := by
  simp only [commutator, anticommutator]
  noncomm_ring

/-- The ordered dual-after-primal transport composition splits into the
Lie-square, minus the Jordan-square, and the exact mixed commutator defect.
This is the noncommutative form of the Laplacian decomposition; the defect
vanishes only under the additional hypothesis that `h` and `s` commute. -/
theorem dual_after_primal_transport_with_defect (h s x : A) :
    dualTransport h s (primalTransport h s x) =
      commutator h (commutator h x) -
        anticommutator s (anticommutator s x) +
        anticommutator (commutator h s) x := by
  unfold dualTransport primalTransport
  have hMixed := commutator_anticommutator_exchange h s x
  simp only [commutator, anticommutator] at hMixed ⊢
  noncomm_ring

/-- The Lie part is skew-adjoint for every cyclic additive functional. -/
theorem cyclic_lie_integration_by_parts {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ) (h x y : A) :
    τ (commutator h x * y) + τ (x * commutator h y) = 0 := by
  have hleft : τ (commutator h x * y) =
      τ (h * (x * y)) - τ (x * (h * y)) := by
    simp only [commutator, sub_mul, map_sub, mul_assoc]
  have hright : τ (x * commutator h y) =
      τ (x * (h * y)) - τ (x * (y * h)) := by
    simp only [commutator, mul_sub, map_sub]
  rw [hleft, hright]
  have hcyc : τ (h * (x * y)) = τ (x * (y * h)) := by
    simpa only [mul_assoc] using hτ h (x * y)
  rw [hcyc]
  abel

/-- The Jordan part is self-adjoint for the cyclic pairing. -/
theorem cyclic_jordan_integration_by_parts {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ) (s x y : A) :
    τ (anticommutator s x * y) = τ (x * anticommutator s y) := by
  have hleft : τ (anticommutator s x * y) =
      τ (s * (x * y)) + τ ((x * s) * y) := by
    simp only [anticommutator, add_mul, map_add, mul_assoc]
  have hright : τ (x * anticommutator s y) =
      τ ((x * s) * y) + τ (x * (y * s)) := by
    simp only [anticommutator, mul_add, map_add, mul_assoc]
  rw [hleft, hright]
  have hcyc : τ (s * (x * y)) = τ (x * (y * s)) := by
    simpa only [mul_assoc] using hτ s (x * y)
  rw [hcyc]
  abel

/-- Opposite-sign Lie--Jordan transports are exactly dual under every cyclic
operator pairing. -/
theorem primal_dual_cyclic_compatibility {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclicFunctional τ) (h s x y : A) :
    τ (primalTransport h s x * y) + τ (x * dualTransport h s y) = 0 := by
  have hLie := cyclic_lie_integration_by_parts τ hτ h x y
  have hJordan := cyclic_jordan_integration_by_parts τ hτ s x y
  change τ ((commutator h x + anticommutator s x) * y) +
    τ (x * (commutator h y - anticommutator s y)) = 0
  have hfirst : τ ((commutator h x + anticommutator s x) * y) =
      τ (commutator h x * y) + τ (anticommutator s x * y) := by
    rw [add_mul, map_add]
  have hsecond : τ (x * (commutator h y - anticommutator s y)) =
      τ (x * commutator h y) - τ (x * anticommutator s y) := by
    rw [mul_sub, map_sub]
  calc
    _ = τ (commutator h x * y) + τ (anticommutator s x * y) +
        (τ (x * commutator h y) - τ (x * anticommutator s y)) := by
      rw [hfirst, hsecond]
    _ = (τ (commutator h x * y) + τ (x * commutator h y)) +
        (τ (anticommutator s x * y) - τ (anticommutator s x * y)) := by
      rw [← hJordan]
      abel
    _ = 0 := by rw [hLie]; simp

/-- Operator-valued divergence for a finite family of generators and fluxes.
The sum remains inside the noncommutative operator algebra. -/
def operatorDivergence {ι : Type*} [Fintype ι]
    (H J : ι → A) : A :=
  ∑ i, commutator (H i) (J i)

/-- The value of an inner-derivation divergence is invisible to every cyclic
additive functional, without choosing a matrix trace or a basis. -/
theorem cyclicFunctional_operatorDivergence_eq_zero {R ι : Type*}
    [AddCommGroup R] [Fintype ι] (τ : A →+ R)
    (hτ : IsCyclicFunctional τ) (H J : ι → A) :
    τ (operatorDivergence H J) = 0 := by
  unfold operatorDivergence
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact functional_commutator_zero τ hτ (H i) (J i)

/-- The operator-valued inner-derivation Laplacian is the divergence of its
own gradient flux. It remains a sum of ordered double commutators in `A`. -/
def innerDerivationLaplacian {ι : Type*} [Fintype ι]
    (H : ι → A) (x : A) : A :=
  ∑ i, commutator (H i) (commutator (H i) x)

end InfoGeometry.OperatorAlgebra.NoncommutativeContextInteraction
