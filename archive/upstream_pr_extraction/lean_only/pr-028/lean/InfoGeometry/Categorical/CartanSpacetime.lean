import Mathlib.Tactic

/-!
# Finite algebraic Cartan-spacetime 2-cell atoms

This module records the theorem-safe algebraic core of the proposed
Cartan-spacetime categorical picture directly with mathlib's canonical function
identity `id`, composition `∘`, and ordinary functions.  It introduces no local
transport, covariance, composition, or trace wrapper definitions.

The content is finite and algebraic:

* `id` is left/right covariant for supplied actions;
* composition preserves explicitly stated covariance equations;
* function composition has left/right identity and associativity;
* an explicitly supplied trace-invariance hypothesis is stable after composing
  with `id`.

No Connes correspondence, Radon--Nikodym cocycle, GNS vacuum, braid-group
representation, Type III factor, or invertible groupoid theorem is asserted.
-/

set_option autoImplicit false

namespace InfoGeometry.Categorical.CartanSpacetime

/-- The identity function is left-covariant for any supplied left action. -/
theorem id_connection_left_covariant {A M : Type*} (left_action : A → M → M) :
    ∀ (a : A) (m : M), id (left_action a m) = left_action a (id m) := by
  intro _ _
  rfl

/-- The identity function is right-covariant for any supplied right action. -/
theorem id_connection_right_covariant {A M : Type*} (right_action : M → A → M) :
    ∀ (m : M) (a : A), id (right_action m a) = right_action (id m) a := by
  intro _ _
  rfl

/-- Composition preserves left covariance. -/
theorem comp_connection_left_covariant {A M : Type*}
    (left_action : A → M → M) (c1 c2 : M → M)
    (h1 : ∀ (a : A) (m : M), c1 (left_action a m) = left_action a (c1 m))
    (h2 : ∀ (a : A) (m : M), c2 (left_action a m) = left_action a (c2 m)) :
    ∀ (a : A) (m : M), (c1 ∘ c2) (left_action a m) = left_action a ((c1 ∘ c2) m) := by
  intro a m
  rw [Function.comp_apply, h2 a m, h1 a (c2 m), Function.comp_apply]

/-- Composition preserves right covariance. -/
theorem comp_connection_right_covariant {A M : Type*}
    (right_action : M → A → M) (c1 c2 : M → M)
    (h1 : ∀ (m : M) (a : A), c1 (right_action m a) = right_action (c1 m) a)
    (h2 : ∀ (m : M) (a : A), c2 (right_action m a) = right_action (c2 m) a) :
    ∀ (m : M) (a : A), (c1 ∘ c2) (right_action m a) = right_action ((c1 ∘ c2) m) a := by
  intro m a
  rw [Function.comp_apply, h2 m a, h1 (c2 m) a, Function.comp_apply]

/-- Identity coherence: composing any function with `id` on the right changes nothing. -/
theorem cocycle_identity {M : Type*} (c : M → M) :
    c ∘ id = c := by
  funext x
  rfl

/-- Left identity coherence for function composition. -/
theorem cocycle_left_identity {M : Type*} (c : M → M) :
    id ∘ c = c := by
  funext x
  rfl

/-- Associativity coherence for function composition. -/
theorem cocycle_composition {M : Type*} (c1 c2 c3 : M → M) :
    (c1 ∘ c2) ∘ c3 = c1 ∘ (c2 ∘ c3) := by
  funext x
  rfl

/-- Conservation of unnormalized state counting after composing with `id`. -/
theorem trace_conservation {M : Type*} (c : M → M) (tr : M → ℕ)
    (h_inv : ∀ x : M, tr (c x) = tr x) :
    ∀ x : M, tr ((c ∘ id) x) = tr x := by
  intro x
  rw [cocycle_identity c]
  exact h_inv x

end InfoGeometry.Categorical.CartanSpacetime
