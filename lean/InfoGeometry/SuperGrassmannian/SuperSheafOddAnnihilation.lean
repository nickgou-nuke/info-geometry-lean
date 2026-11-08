/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Signed pullback invariance and fixed-point two-torsion

The carrier is a triple of ring-valued functions. Its middle component changes
sign under pullback, while the other two components do not. No topology,
restriction maps, sheaf gluing, quotient space, or super-Grassmannian is
constructed here. Historical declaration names are retained for existing users.

At a fixed point, invariance forces twice the middle component to vanish.
Vanishing of the component itself requires absence of two-torsion. In
characteristic two even the identity pullback fixes every triple, so invariance
alone cannot filter out a nonzero middle component. The ring may be
noncommutative, including a matrix or operator ring.
-/

namespace InfoGeometry.SuperGrassmannian.SheafAnnihilation

variable {M R : Type*} [Ring R]

/-- Three independent ring-valued functions, with a designated sign-changing component. -/
@[ext]
structure GradedSuperField (M R : Type*) where
  body  : M → R
  odd1  : M → R
  even2 : M → R

/-- Pull back all three functions and negate the middle component. -/
def moebiusPullback (invM : M → M) (f : GradedSuperField M R) : GradedSuperField M R where
  body  := fun T => f.body (invM T)
  odd1  := fun T => - f.odd1 (invM T)
  even2 := fun T => f.even2 (invM T)

/-- Fixed points of the signed pullback. This predicate asserts no sheaf structure. -/
def IsQuotientSheafSection (invM : M → M) (f : GradedSuperField M R) : Prop :=
  moebiusPullback invM f = f

/-! ### Section 1: Involutive Properties of the Pullback -/

/-- An involutive base map induces an involutive signed pullback. -/
theorem moebiusPullback_involutive (invM : M → M) (h_inv : ∀ T, invM (invM T) = T)
    (f : GradedSuperField M R) :
    moebiusPullback invM (moebiusPullback invM f) = f := by
  dsimp [moebiusPullback]
  ext T
  · simp [h_inv T]
  · simp [h_inv T]
  · simp [h_inv T]

/-! ### Fixed-point two-torsion -/

/-- The unconditional fixed-point conclusion is two-torsion, not vanishing. -/
theorem odd_component_two_torsion_at_fixed
    (invM : M → M) (x : M) (hx : invM x = x)
    (f : GradedSuperField M R) (hf : IsQuotientSheafSection invM f) :
    2 * f.odd1 x = 0 := by
  have he := congrArg (fun g : GradedSuperField M R => g.odd1 x) hf
  change -f.odd1 (invM x) = f.odd1 x at he
  rw [hx] at he
  have hz := add_neg_cancel (f.odd1 x)
  rw [he] at hz
  simpa only [two_mul] using hz

/-- For the identity base map, invariance is exactly pointwise two-torsion
of the middle component; the other two functions are unrestricted. -/
theorem identity_pullback_invariant_iff (f : GradedSuperField M R) :
    IsQuotientSheafSection id f ↔ ∀ x, 2 * f.odd1 x = 0 := by
  constructor
  · intro hf x
    exact odd_component_two_torsion_at_fixed id x rfl f hf
  · intro h
    change moebiusPullback id f = f
    ext x
    · rfl
    · change -f.odd1 x = f.odd1 x
      apply neg_eq_iff_add_eq_zero.mpr
      simpa only [two_mul] using h x
    · rfl

/-- In a characteristic-two ring the signed identity pullback fixes every
triple, including those with nonzero middle components. -/
theorem identity_pullback_invariant_of_two_eq_zero (h2 : (2 : R) = 0)
    (f : GradedSuperField M R) : IsQuotientSheafSection id f := by
  apply (identity_pullback_invariant_iff f).mpr
  intro x
  rw [h2, zero_mul]

/-- At a fixed point, the sign-changing component vanishes if the ring has no two-torsion. -/
theorem odd_anomaly_annihilated_at_crosscap
    (invM : M → M) (T_crosscap : M) (h_fixed : invM T_crosscap = T_crosscap)
    (f : GradedSuperField M R) (h_sec : IsQuotientSheafSection invM f)
    (h_no_two_torsion : ∀ x : R, 2 * x = 0 → x = 0) :
    f.odd1 T_crosscap = 0 := by
  exact h_no_two_torsion _
    (odd_component_two_torsion_at_fixed invM T_crosscap h_fixed f h_sec)

/-! ### Unchanged components at fixed points -/

/-- The first component evaluates unchanged at a fixed point. -/
theorem even_body_invariant_at_crosscap
    (invM : M → M) (T_crosscap : M) (h_fixed : invM T_crosscap = T_crosscap)
    (f : GradedSuperField M R) :
    (moebiusPullback invM f).body T_crosscap = f.body T_crosscap := by
  dsimp [moebiusPullback]
  rw [h_fixed]

/-- The third component evaluates unchanged at a fixed point. No product of odd elements is asserted. -/
theorem paired_even2_invariant_at_crosscap
    (invM : M → M) (T_crosscap : M) (h_fixed : invM T_crosscap = T_crosscap)
    (f : GradedSuperField M R) :
    (moebiusPullback invM f).even2 T_crosscap = f.even2 T_crosscap := by
  dsimp [moebiusPullback]
  rw [h_fixed]

/-- A nonzero middle component at a fixed point obstructs invariance in a ring without two-torsion. -/
theorem isolated_odd_anomaly_rejected
    (invM : M → M) (T_crosscap : M) (h_fixed : invM T_crosscap = T_crosscap)
    (f : GradedSuperField M R) (h_odd_nonzero : f.odd1 T_crosscap ≠ 0)
    (h_no_two_torsion : ∀ x : R, 2 * x = 0 → x = 0) :
    ¬ IsQuotientSheafSection invM f := by
  intro h_sec
  have h_zero := odd_anomaly_annihilated_at_crosscap invM T_crosscap h_fixed f h_sec h_no_two_torsion
  exact h_odd_nonzero h_zero

/-! ### Invariants with zero middle component -/

/-- A triple with zero middle component and arbitrary first and third functions. -/
def makeBalancedSyzygy (b e2 : M → R) : GradedSuperField M R where
  body  := b
  odd1  := fun _ => 0
  even2 := e2

/-- Invariant first and third functions and a zero middle function give an
invariant triple. This is a fixed-point statement, not a sheaf gluing theorem. -/
theorem balanced_syzygy_is_sheaf_section
    (invM : M → M) (b e2 : M → R)
    (hb : ∀ T, b (invM T) = b T) (he2 : ∀ T, e2 (invM T) = e2 T) :
    IsQuotientSheafSection invM { body := b, odd1 := fun _ => 0, even2 := e2 } := by
  dsimp [IsQuotientSheafSection, moebiusPullback]
  ext T
  · exact hb T
  · simp
  · exact he2 T

end InfoGeometry.SuperGrassmannian.SheafAnnihilation
