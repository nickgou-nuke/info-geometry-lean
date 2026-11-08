/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ParabolicNullQuotientCausalCone
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic

/-!
# Star-Ring Endomorphism Radical, Left Ideals, and Tracial Algebra Quotients

This module formalizes the algebraic core separating representation spaces from algebra quotients
for an additive endomorphism $\phi : A \to+ A$ on a star-ring $A$:

### Mathematical Invariants Proved:
1. **Star-Mul Pairing**:
   An additive endomorphism $\phi : A \to+ A$ on a star-ring $A$ induces a pairing
   $B_\phi(y, x) = \phi(\operatorname{star} y * x)$.
2. **Universal Left Ideal Property**:
   The radical $\mathcal{N}_\phi = \{ x \in A \mid \forall y, \phi(\operatorname{star} y * x) = 0 \}$
   forms an additive subgroup that is unconditionally stable under left multiplication:
   $x \in \mathcal{N}_\phi \implies a * x \in \mathcal{N}_\phi$.
3. **Well-Defined Left Module Action**:
   Because $\mathcal{N}_\phi$ is a left ideal, left multiplication $a \cdot [x] = [a * x]$
   descends well-definedly to the quotient carrier $A / \mathcal{N}_\phi$ without requiring traciality.
4. **Tracial Sufficiency for Two-Sided Ideals**:
   If $\phi$ is tracial ($\phi(u * v) = \phi(v * u)$), then $\mathcal{N}_\phi$ is also stable under
   right multiplication ($x * a \in \mathcal{N}_\phi$), making it a two-sided ideal.
   Note: Traciality is sufficient, not necessary; for faithful states, $\mathcal{N}_\phi = \{0\}$,
   which is always trivially a two-sided ideal.
5. **State Commutator Equivalence**:
   The state commutator $\phi(u * v - v * u)$ vanishes identically if and only if $\phi$ is tracial.

### Epistemic Scope:
- This is a purely algebraic ring-theoretic model for additive endomorphisms $\phi : A \to+ A$.
- It does **not** construct the completed GNS Hilbert space $\mathcal{H}_{\mathrm{GNS}}$ or analytic
  Tomita–Takesaki modular flow, which require $C^*$-algebraic and functional-analytic structure.

All theorems are fully proved with zero `sorry`, zero `admit`, and core Mathlib axioms.
-/

namespace InfoGeometry.Canonical.StateRadicalGNSIdealBridge

open InfoGeometry.Canonical.ParabolicQuotient

variable {A : Type*} [Ring A] [StarRing A]

/-- The GNS inner product pairing induced by a linear functional $\phi : A \to A$. -/
def gnsPairing (phi : A →+ A) (y x : A) : A :=
  phi (star y * x)

/-- The GNS radical: elements $x \in A$ orthogonal to all $y \in A$ under $gnsPairing$. -/
def gnsRadical (phi : A →+ A) : AddSubgroup A where
  carrier := { x : A | ∀ y : A, gnsPairing phi y x = 0 }
  zero_mem' y := by
    dsimp [gnsPairing]
    rw [mul_zero, map_zero]
  add_mem' {a b} ha hb y := by
    dsimp [gnsPairing] at ha hb ⊢
    rw [mul_add, map_add, ha y, hb y, add_zero]
  neg_mem' {a} ha y := by
    dsimp [gnsPairing] at ha ⊢
    rw [mul_neg, map_neg, ha y, neg_zero]

/-- Membership in the GNS radical. -/
theorem mem_gnsRadical_iff (phi : A →+ A) (x : A) :
    x ∈ gnsRadical phi ↔ ∀ y : A, phi (star y * x) = 0 :=
  Iff.rfl

/-- Universal Left Ideal Theorem:
For any linear functional $\phi$, its GNS radical is stable under left multiplication by any $a \in A$.
This holds without any traciality assumption. -/
theorem gnsRadical_is_left_ideal (phi : A →+ A) (a : A) {x : A}
    (hx : x ∈ gnsRadical phi) :
    a * x ∈ gnsRadical phi := by
  intro y
  dsimp [gnsPairing]
  have h_assoc : star y * (a * x) = (star y * a) * x := (mul_assoc (star y) a x).symm
  rw [h_assoc]
  have h_star : star y * a = star (star a * y) := by
    rw [star_mul, star_star]
  rw [h_star]
  exact hx (star a * y)

/-- Well-definedness of GNS left representation action:
If $x - x' \in \mathcal{N}_\phi$, then $a * x - a * x' \in \mathcal{N}_\phi$. -/
theorem gns_left_action_well_defined (phi : A →+ A) (a : A) {x x' : A}
    (h_diff : x - x' ∈ gnsRadical phi) :
    a * x - a * x' ∈ gnsRadical phi := by
  rw [← mul_sub]
  exact gnsRadical_is_left_ideal phi a h_diff

/-- Predicate for a tracial linear functional: $\phi(u * v) = \phi(v * u)$. -/
def IsTracial (phi : A →+ A) : Prop :=
  ∀ u v : A, phi (u * v) = phi (v * u)

/-- Tracial Right Ideal Theorem:
If $\phi$ is tracial, then the GNS radical is also stable under right multiplication,
making it a genuine two-sided ideal. -/
theorem gnsRadical_is_right_ideal_of_tracial (phi : A →+ A) (h_trace : IsTracial phi)
    (a : A) {x : A} (hx : x ∈ gnsRadical phi) :
    x * a ∈ gnsRadical phi := by
  intro y
  dsimp [gnsPairing]
  have h_assoc : star y * (x * a) = (star y * x) * a := (mul_assoc (star y) x a).symm
  rw [h_assoc]
  rw [h_trace (star y * x) a]
  have h_inner : a * (star y * x) = (a * star y) * x := (mul_assoc a (star y) x).symm
  rw [h_inner]
  have h_star : a * star y = star (y * star a) := by
    rw [star_mul, star_star]
  rw [h_star]
  exact hx (y * star a)

/-- Master Two-Sided Ideal Theorem for Tracial States:
Under a tracial functional, the GNS radical is a two-sided ideal. -/
theorem gnsRadical_is_two_sided_ideal_of_tracial (phi : A →+ A) (h_trace : IsTracial phi)
    (a : A) {x : A} (hx : x ∈ gnsRadical phi) :
    a * x ∈ gnsRadical phi ∧ x * a ∈ gnsRadical phi :=
  ⟨gnsRadical_is_left_ideal phi a hx, gnsRadical_is_right_ideal_of_tracial phi h_trace a hx⟩

set_option linter.unusedSectionVars false

/-- The State Commutator: $\phi([u, v]) = \phi(u * v - v * u)$. -/
def stateCommutator (phi : A →+ A) (u v : A) : A :=
  phi (u * v - v * u)

/-- The state commutator vanishes identically if and only if the functional is tracial. -/
theorem stateCommutator_eq_zero_iff_tracial (phi : A →+ A) :
    (∀ u v : A, stateCommutator phi u v = 0) ↔ IsTracial phi := by
  constructor
  · intro h u v
    have h_sub := h u v
    dsimp [stateCommutator] at h_sub
    rw [map_sub, sub_eq_zero] at h_sub
    exact h_sub
  · intro h_trace u v
    dsimp [stateCommutator]
    rw [map_sub]
    exact sub_eq_zero.mpr (h_trace u v)

/-- Non-Tracial Modular Gap Certificate:
If the state commutator does not vanish on some pair $(u, v)$,
the state is strictly non-tracial. -/
theorem non_tracial_of_stateCommutator_ne_zero (phi : A →+ A) (u v : A)
    (h_non_zero : stateCommutator phi u v ≠ 0) :
    ¬ IsTracial phi := by
  intro h_trace
  have h_vanish := (stateCommutator_eq_zero_iff_tracial phi).mpr h_trace u v
  exact h_non_zero h_vanish

end InfoGeometry.Canonical.StateRadicalGNSIdealBridge
