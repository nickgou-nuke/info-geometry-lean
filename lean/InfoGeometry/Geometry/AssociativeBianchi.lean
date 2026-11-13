/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.AssociativeGaugeConnection

/-!
# Adjoint connections and cyclic Bianchi on an associative algebra

The coefficient algebra is an arbitrary ring. The base operators are native
linear endomorphisms satisfying the ordered `IsLeibniz` rule from
`AssociativeGaugeConnection`. Taking the scalar base to be `ℤ` covers every
ring without a commutativity assumption on its elements.

The adjoint connection uses the existing `innerDerivative`. Its commutator
and the cyclic Bianchi sum are first computed with their base-commutator
defects retained. Pairwise commuting base operators then give the usual
identities. The three operators may be zero or linearly dependent, and the
three potentials are arbitrary. The Bianchi equality is an equality of
algebra elements, derived by the Leibniz rule; it is not inferred from
vanishing of an inner derivation.

The existing owner supplies fundamental connections, affine unit gauge
potentials, and exact curvature gauge covariance. The final square expansion
retains both ordered mixed products and makes no trace or positivity claim.
-/

noncomputable section

namespace InfoGeometry.Geometry.AssociativeGaugeConnection

variable {R A : Type*} [Ring R] [Ring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- The connection on the adjoint module, `D + ad(a)`. -/
def adjointCovariantDerivative (D : Module.End R A) (a : A) : Module.End R A :=
  D + innerDerivative (R := R) a

@[simp] theorem adjointCovariantDerivative_apply
    (D : Module.End R A) (a x : A) :
    adjointCovariantDerivative D a x = D x + (a * x - x * a) := rfl

/-- The adjoint connection is the existing fundamental connection minus
right multiplication by the same potential. -/
theorem adjointCovariantDerivative_eq_covariantDerivative_sub
    (D : Module.End R A) (a : A) :
    adjointCovariantDerivative D a =
      covariantDerivative D a - LinearMap.mulRight R a := by
  ext x
  change D x + (a * x - x * a) = (D x + a * x) - x * a
  noncomm_ring

/-- An adjoint connection preserves the associative Leibniz rule. -/
theorem adjointCovariantDerivative_isLeibniz
    (D : Module.End R A) (hD : IsLeibniz D) (a : A) :
    IsLeibniz (adjointCovariantDerivative D a) := by
  intro x y
  simp only [adjointCovariantDerivative_apply, hD x y]
  noncomm_ring

/-- The full adjoint commutator retains the commutator of the base operators. -/
theorem adjoint_commutator_action
    (D E : Module.End R A) (hD : IsLeibniz D) (hE : IsLeibniz E)
    (a b x : A) :
    adjointCovariantDerivative D a (adjointCovariantDerivative E b x) -
        adjointCovariantDerivative E b (adjointCovariantDerivative D a x) =
      (D (E x) - E (D x)) +
        (curvature D E a b * x - x * curvature D E a b) := by
  simp only [adjointCovariantDerivative_apply, map_add, map_sub,
    hD b x, hD x b, hE a x, hE x a, curvature]
  noncomm_ring

/-- With commuting base operators, the adjoint commutator is `ad(F)`. -/
theorem adjoint_curvature_action
    (D E : Module.End R A) (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x)) (a b x : A) :
    adjointCovariantDerivative D a (adjointCovariantDerivative E b x) -
        adjointCovariantDerivative E b (adjointCovariantDerivative D a x) =
      curvature D E a b * x - x * curvature D E a b := by
  simpa only [hcomm x, sub_self, zero_add] using
    adjoint_commutator_action D E hD hE a b x

/-- The cyclic covariant curvature sum has exactly the indicated defects
when the three base operators are not assumed to commute. -/
theorem cyclicBianchi_defect
    (D E G : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E) (hG : IsLeibniz G)
    (a b c : A) :
    adjointCovariantDerivative D a (curvature E G b c) +
        adjointCovariantDerivative E b (curvature G D c a) +
        adjointCovariantDerivative G c (curvature D E a b) =
      (D (E c) - E (D c)) + (E (G a) - G (E a)) +
        (G (D b) - D (G b)) := by
  simp only [adjointCovariantDerivative_apply, curvature, map_add, map_sub,
    hD b c, hD c b, hE c a, hE a c, hG a b, hG b a]
  noncomm_ring

/-- Exact cyclic second Bianchi for arbitrary potentials and pairwise
commuting associative derivations. No faithful or independent direction
representation is required. -/
theorem cyclicBianchi
    (D E G : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E) (hG : IsLeibniz G)
    (hDE : ∀ x, D (E x) = E (D x))
    (hEG : ∀ x, E (G x) = G (E x))
    (hGD : ∀ x, G (D x) = D (G x))
    (a b c : A) :
    adjointCovariantDerivative D a (curvature E G b c) +
        adjointCovariantDerivative E b (curvature G D c a) +
        adjointCovariantDerivative G c (curvature D E a b) = 0 := by
  simpa only [hDE c, hEG a, hGD b, sub_self, add_zero] using
    cyclicBianchi_defect D E G hD hE hG a b c

omit [SMulCommClass R A A] [IsScalarTower R A A] in
/-- The raw curvature square keeps the two ordered cubic terms and the
quartic commutator square. This identity needs neither Leibniz nor commuting
base operators. -/
theorem curvature_square_expansion
    (D E : Module.End R A) (a b : A) :
    curvature D E a b * curvature D E a b =
      (D b - E a) * (D b - E a) +
        (D b - E a) * (a * b - b * a) +
        (a * b - b * a) * (D b - E a) +
        (a * b - b * a) * (a * b - b * a) := by
  simp only [curvature]
  noncomm_ring

end InfoGeometry.Geometry.AssociativeGaugeConnection
