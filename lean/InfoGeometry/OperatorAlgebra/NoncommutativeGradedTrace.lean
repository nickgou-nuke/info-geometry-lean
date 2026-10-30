/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Algebra.Star.Basic

/-!
# Graded cyclic traces in noncommutative operator algebras

The cyclic trace identities used in finite-dimensional McKean--Singer-style
calculations are stated here for arbitrary associative operator rings and an
additive cyclic functional. These are algebraic cancellation results; they do
not assert an analytic index theorem or spectral pairing.
-/

namespace InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace

variable {A : Type*} [Ring A]

/-- The commutator of two operators in an associative ring. -/
def operatorCommutator (x y : A) : A := x * y - y * x

/-- The anticommutator of two operators in an associative ring. -/
def operatorAnticommutator (x y : A) : A := x * y + y * x

/-- An additive functional is cyclic when it is invariant under a two-factor
cyclic rotation. -/
def IsCyclic {R : Type*} [AddCommGroup R] (τ : A →+ R) : Prop :=
  ∀ x y, τ (x * y) = τ (y * x)

/-- A cyclic additive functional sends the product of an
anticommuting operator pair to 2-torsion. No division by two, matrix trace,
or torsion-freeness assumption is needed. -/
theorem cyclic_anticommuting_product_two_torsion {R : Type*}
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ) {x y : A}
    (hanti : x * y + y * x = 0) :
    τ (x * y) + τ (x * y) = 0 := by
  have hyx : y * x = -(x * y) := eq_neg_of_add_eq_zero_right hanti
  have hneg : τ (x * y) = -τ (x * y) := by
    calc
      τ (x * y) = τ (y * x) := hτ x y
      _ = τ (-(x * y)) := by rw [hyx]
      _ = -τ (x * y) := map_neg τ _
  calc
    τ (x * y) + τ (x * y) = τ (x * y) + -τ (x * y) :=
      congrArg (fun z => τ (x * y) + z) hneg
    _ = 0 := add_neg_cancel _

/-- The graded trace determined by an operator grading and a cyclic
functional. -/
def gradedTrace {R : Type*} [AddCommGroup R] (τ : A →+ R) (γ x : A) : R :=
  τ (γ * x)

/-- A grading-even operator has zero graded trace on any commutator. -/
theorem gradedTrace_commutator_eq_zero {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclic τ) {γ a b : A} (hγa : γ * a = a * γ) :
    gradedTrace τ γ (operatorCommutator a b) = 0 := by
  have hcycle : τ ((γ * b) * a) = τ ((a * γ) * b) := by
    calc
      τ ((γ * b) * a) = τ (a * (γ * b)) := hτ _ _
      _ = τ ((a * γ) * b) := by rw [mul_assoc]
  unfold gradedTrace operatorCommutator
  calc
    τ (γ * (a * b - b * a)) = τ (γ * (a * b)) - τ (γ * (b * a)) := by
      rw [mul_sub, map_sub]
    _ = τ ((γ * a) * b) - τ ((γ * b) * a) := by
      rw [← mul_assoc, ← mul_assoc]
    _ = τ ((a * γ) * b) - τ ((a * γ) * b) := by rw [hcycle, hγa]
    _ = 0 := sub_self _

/-- The graded trace annihilates the anticommutator of an odd operator and an
even operator. -/
theorem gradedTrace_anticommutator_eq_zero {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclic τ) {γ d x : A}
    (hγd : γ * d = -(d * γ)) (hγx : γ * x = x * γ) :
    gradedTrace τ γ (operatorAnticommutator d x) = 0 := by
  have hcycle : τ ((x * γ) * d) = τ (d * (x * γ)) :=
    hτ (x * γ) d
  have hfirst : τ ((γ * d) * x) = -τ (d * (x * γ)) := by
    calc
      τ ((γ * d) * x) = τ (-((d * γ) * x)) := by rw [hγd, neg_mul]
      _ = -τ ((d * γ) * x) := by rw [map_neg]
      _ = -τ (d * (γ * x)) := by congr 2; rw [mul_assoc]
      _ = -τ (d * (x * γ)) := by rw [hγx]
  have hsecond : τ ((γ * x) * d) = τ (d * (x * γ)) := by
    calc
      τ ((γ * x) * d) = τ ((x * γ) * d) := by rw [hγx]
      _ = τ (d * (x * γ)) := hcycle
  unfold gradedTrace operatorAnticommutator
  calc
    τ (γ * (d * x + x * d)) =
        τ ((γ * d) * x) + τ ((γ * x) * d) := by
      rw [mul_add, map_add, ← mul_assoc, ← mul_assoc]
    _ = 0 := by rw [hfirst, hsecond]; exact neg_add_cancel _

/-- The cyclic graded trace of the square of an odd operator vanishes when
the trace range has no 2-torsion. This is the algebraic cancellation behind
finite McKean--Singer calculations; no heat kernel or index is inferred. -/
theorem gradedTrace_odd_square_eq_zero {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclic τ)
    (h_two_torsion_free : ∀ r : R, r + r = 0 → r = 0)
    {γ d : A} (h_odd : γ * d + d * γ = 0) :
    gradedTrace τ γ (d * d) = 0 := by
  have h_dγ : d * γ = -(γ * d) := eq_neg_of_add_eq_zero_right h_odd
  have htrace : τ (γ * (d * d)) = -τ (γ * (d * d)) := by
    calc
      τ (γ * (d * d)) = τ ((γ * d) * d) := by rw [← mul_assoc]
      _ = τ (d * (γ * d)) := hτ (γ * d) d
      _ = τ ((d * γ) * d) := by rw [mul_assoc]
      _ = τ ((-(γ * d)) * d) := by rw [h_dγ]
      _ = τ (-((γ * d) * d)) := by rw [neg_mul]
      _ = -τ (γ * (d * d)) := by rw [map_neg, mul_assoc]
  have hdouble : τ (γ * (d * d)) + τ (γ * (d * d)) = 0 := by
    calc
      τ (γ * (d * d)) + τ (γ * (d * d)) =
          τ (γ * (d * d)) + -τ (γ * (d * d)) := by
        exact congrArg (fun z => τ (γ * (d * d)) + z) htrace
      _ = 0 := add_neg_cancel _
  exact h_two_torsion_free _ hdouble

/-- The two diagonal Peirce corners of an operator. -/
def evenCorner (p x : A) : A := p * x * p + (1 - p) * x * (1 - p)

/-- The two off-diagonal Peirce corners of an operator. -/
def oddCorner (p x : A) : A := p * x * (1 - p) + (1 - p) * x * p

/-- An even grading operator has zero cyclic graded trace on the odd Peirce
corner of any idempotent commuting with that grading. -/
theorem gradedTrace_oddCorner_eq_zero {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclic τ) {γ p x : A}
    (hp : p * p = p) (hγp : γ * p = p * γ) :
    gradedTrace τ γ (oddCorner p x) = 0 := by
  let q : A := 1 - p
  have hpq : p * q = 0 := by
    dsimp [q]
    noncomm_ring [hp]
  have hqp : q * p = 0 := by
    dsimp [q]
    noncomm_ring [hp]
  have hγq : γ * q = q * γ := by
    dsimp [q]
    noncomm_ring [hγp]
  have hupper : τ (γ * (p * x * q)) = 0 := by
    calc
      τ (γ * (p * x * q)) = τ ((q * γ) * (p * x)) := by
        rw [show γ * (p * x * q) = (γ * (p * x)) * q by noncomm_ring]
        calc
          τ ((γ * (p * x)) * q) = τ (q * (γ * (p * x))) := hτ _ _
          _ = τ ((q * γ) * (p * x)) := by rw [← mul_assoc]
      _ = 0 := by
        rw [← hγq]
        calc
          τ ((γ * q) * (p * x)) = τ (γ * (q * p) * x) := by
            congr 1; noncomm_ring
          _ = τ 0 := by simp [hqp]
          _ = 0 := map_zero τ
  have hlower : τ (γ * (q * x * p)) = 0 := by
    calc
      τ (γ * (q * x * p)) = τ ((p * γ) * (q * x)) := by
        rw [show γ * (q * x * p) = (γ * (q * x)) * p by noncomm_ring]
        calc
          τ ((γ * (q * x)) * p) = τ (p * (γ * (q * x))) := hτ _ _
          _ = τ ((p * γ) * (q * x)) := by rw [← mul_assoc]
      _ = 0 := by
        rw [← hγp]
        calc
          τ ((γ * p) * (q * x)) = τ (γ * (p * q) * x) := by
            congr 1; noncomm_ring
          _ = τ 0 := by simp [hpq]
          _ = 0 := map_zero τ
  unfold gradedTrace oddCorner
  simp only [mul_add, map_add]
  rw [hupper, hlower, add_zero]

/-- A cyclic additive functional vanishes on each directed Peirce corner
separately. This is stronger than vanishing on their sum, which would not
justify a termwise conclusion over an arbitrary additive target. -/
theorem cyclicFunctional_directedCorners_eq_zero {R : Type*}
    [AddCommGroup R] (τ : A →+ R) (hτ : IsCyclic τ) {p : A}
    (hp : p * p = p) (x : A) :
    τ (p * x * (1 - p)) = 0 ∧ τ ((1 - p) * x * p) = 0 := by
  have hpq : p * (1 - p) = 0 := by noncomm_ring [hp]
  have hqp : (1 - p) * p = 0 := by noncomm_ring [hp]
  constructor
  · calc
      τ (p * x * (1 - p)) = τ ((1 - p) * (p * x)) :=
        hτ (p * x) (1 - p)
      _ = τ (((1 - p) * p) * x) := by
        congr 1
        exact (mul_assoc (1 - p) p x).symm
      _ = 0 := by simp [hqp]
  · calc
      τ ((1 - p) * x * p) = τ (p * ((1 - p) * x)) :=
        hτ ((1 - p) * x) p
      _ = τ ((p * (1 - p)) * x) := by
        congr 1
        exact (mul_assoc p (1 - p) x).symm
      _ = 0 := by simp [hpq]

/-- The graded trace is unchanged by removing the off-diagonal Peirce corner.
This is a cyclic-trace identity in an arbitrary associative operator ring. -/
theorem gradedTrace_evenCorner_eq {R : Type*} [AddCommGroup R]
    (τ : A →+ R) (hτ : IsCyclic τ) {γ p x : A}
    (hp : p * p = p) (hγp : γ * p = p * γ) :
    gradedTrace τ γ (evenCorner p x) = gradedTrace τ γ x := by
  have hdecomp : evenCorner p x + oddCorner p x = x := by
    unfold evenCorner oddCorner
    noncomm_ring [hp]
  have hodd : τ (γ * oddCorner p x) = 0 :=
    gradedTrace_oddCorner_eq_zero τ hτ hp hγp
  change τ (γ * evenCorner p x) = τ (γ * x)
  calc
    τ (γ * evenCorner p x) =
        τ (γ * evenCorner p x) + τ (γ * oddCorner p x) := by rw [hodd]; simp
    _ = τ (γ * (evenCorner p x + oddCorner p x)) := by
      rw [mul_add, map_add]
    _ = τ (γ * x) := by rw [hdecomp]

/-- A finite weighted mixture of unitary conjugations on an associative
operator algebra. -/
def unitaryMixture {R A κ : Type*} [CommSemiring R] [Ring A]
    [Algebra R A] [StarRing A] [Fintype κ]
    (w : κ → R) (U : κ → A) (x : A) : A :=
  ∑ i, w i • (U i * x * star (U i))

/-- Each unitary conjugation preserves a cyclic linear functional. -/
theorem cyclicFunctional_unitaryConjugation {R A : Type*}
    [CommSemiring R] [Ring A] [Algebra R A] [StarRing A]
    (τ : A →ₗ[R] R) (hτ : ∀ a b, τ (a * b) = τ (b * a))
    {u x : A} (hu : star u * u = 1) :
    τ (u * x * star u) = τ x := by
  calc
    τ (u * x * star u) = τ (u * (x * star u)) := by rw [mul_assoc]
    _ = τ ((x * star u) * u) := hτ _ _
    _ = τ (x * (star u * u)) := by rw [mul_assoc]
    _ = τ x := by rw [hu, mul_one]

/-- A normalized finite mixture of unitary conjugations is unital and
preserves every cyclic linear functional. The operator products remain ordered
throughout; no commutative or diagonal carrier is chosen. -/
theorem unitaryMixture_unital_and_cyclicFunctional_preserving
    {R A κ : Type*} [CommSemiring R] [Ring A] [Algebra R A] [StarRing A]
    [Fintype κ] (w : κ → R) (hw : ∑ i, w i = 1) (U : κ → A)
    (hU : ∀ i, star (U i) * U i = 1 ∧ U i * star (U i) = 1)
    (τ : A →ₗ[R] R) (hτ : ∀ a b, τ (a * b) = τ (b * a)) (x : A) :
    unitaryMixture w U 1 = 1 ∧ τ (unitaryMixture w U x) = τ x := by
  constructor
  · unfold unitaryMixture
    calc
      (∑ i, w i • (U i * 1 * star (U i))) = ∑ i, w i • (1 : A) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_one, (hU i).2]
      _ = (∑ i, w i) • (1 : A) := by rw [← Finset.sum_smul]
      _ = 1 := by rw [hw, one_smul]
  · unfold unitaryMixture
    rw [map_sum]
    have hterm : ∀ i, τ (U i * x * star (U i)) = τ x := by
      intro i
      exact cyclicFunctional_unitaryConjugation τ hτ (hU i).1
    simp_rw [map_smul, hterm, ← Finset.sum_smul, hw, one_smul]

end InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
