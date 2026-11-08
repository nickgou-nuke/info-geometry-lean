import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Algebra.ScaleCocycleInvariant

Finite scale-transport lemmas for fractal/operator inductive systems.

This file separates two layers:

* immutable invariants: quantities unchanged by one zoom/bonding step;
* scale cocycles: quantities that change by an additive defect at each step.

It also records the finite algebraic effect of a time-reversal / Möbius /
Cayley-style involutive conjugation: if an observable is invariant under the
original step and under the involution, it is invariant under the conjugated
step.

No colimit, no completion, no analytic continuation, no Type III theorem.
-/

namespace InfoGeometry.Algebra.ScaleCocycleInvariant

open Finset BigOperators

/--
Iterating a finite bonding/zoom step.
-/
def iter {X : Type*} (step : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => step (iter step n x)

@[simp]
theorem iter_zero {X : Type*} (step : X → X) (x : X) :
    iter step 0 x = x := rfl

@[simp]
theorem iter_succ {X : Type*} (step : X → X) (n : Nat) (x : X) :
    iter step (n + 1) x = step (iter step n x) := rfl

/--
If an observable is invariant under one scale step, it is invariant under every
finite number of scale steps.
-/
theorem invariant_iter
    {X Y : Type*}
    (step : X → X)
    (I : X → Y)
    (hI : ∀ x : X, I (step x) = I x) :
    ∀ n : Nat, ∀ x : X, I (iter step n x) = I x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [iter]
  | succ n ih =>
      intro x
      calc
        I (iter step (n + 1) x)
            = I (step (iter step n x)) := rfl
        _ = I (iter step n x) := hI _
        _ = I x := ih x

/--
A scale-dependent potential whose one-step change is an additive cocycle has
a finite telescoping formula along the scale chain.

This is the abstract finite-stage form of:

`renormalized quantity at depth n`
=
`initial quantity`
+
`sum of scale defects`.
-/
theorem potential_iter_eq_sum_cocycle
    {X A : Type*} [AddCommMonoid A]
    (step : X → X)
    (F : X → A)
    (c : X → A)
    (hF : ∀ x : X, F (step x) = F x + c x) :
    ∀ n : Nat, ∀ x : X,
      F (iter step n x) =
        F x + ∑ k ∈ range n, c (iter step k x) := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [iter]
  | succ n ih =>
      intro x
      calc
        F (iter step (n + 1) x)
            = F (step (iter step n x)) := rfl
        _ = F (iter step n x) + c (iter step n x) := hF _
        _ =
          (F x + ∑ k ∈ range n, c (iter step k x)) +
            c (iter step n x) := by
              rw [ih x]
        _ =
          F x + ∑ k ∈ range (n + 1), c (iter step k x) := by
              rw [sum_range_succ]
              ac_rfl

/--
If the scale cocycle vanishes identically, the potential is actually an
immutable invariant along the finite chain.
-/
theorem potential_iter_eq_of_zero_cocycle
    {X A : Type*} [AddCommMonoid A]
    (step : X → X)
    (F : X → A)
    (c : X → A)
    (hF : ∀ x : X, F (step x) = F x + c x)
    (hc : ∀ x : X, c x = 0) :
    ∀ n : Nat, ∀ x : X, F (iter step n x) = F x := by
  intro n x
  rw [potential_iter_eq_sum_cocycle step F c hF n x]
  simp [hc]

/--
A Möbius/Cayley/time-reversal style conjugated step preserves an invariant
whenever the observable is invariant under both the original step and the
involution.

The conjugated step is:

`x ↦ inv (step (inv x))`.
-/
theorem invariant_conjugated_step
    {X Y : Type*}
    (step inv : X → X)
    (I : X → Y)
    (hStep : ∀ x : X, I (step x) = I x)
    (hInv : ∀ x : X, I (inv x) = I x)
    (x : X) :
    I (inv (step (inv x))) = I x := by
  rw [hInv (step (inv x))]
  rw [hStep (inv x)]
  rw [hInv x]

/--
The conjugated scale step preserves the invariant at every finite depth.
-/
theorem invariant_iter_conjugated_step
    {X Y : Type*}
    (step inv : X → X)
    (I : X → Y)
    (hStep : ∀ x : X, I (step x) = I x)
    (hInv : ∀ x : X, I (inv x) = I x) :
    ∀ n : Nat, ∀ x : X,
      I (iter (fun x => inv (step (inv x))) n x) = I x := by
  exact
    invariant_iter
      (fun x => inv (step (inv x)))
      I
      (invariant_conjugated_step step inv I hStep hInv)

end InfoGeometry.Algebra.ScaleCocycleInvariant

/-!
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `invariant_iter` : Proves that scale-step invariant observables are invariant at all finite iteration depths.
- `potential_iter_eq_sum_cocycle` : Proves the finite telescoping potential sum along a scale iteration chain under a scale-dependent additive cocycle.
- `potential_iter_eq_of_zero_cocycle` : Proves that potentials with vanishing scale cocycles are invariants along the iteration chain.
- `invariant_conjugated_step` : Proves one-step invariance under an involutive-conjugated step.
- `invariant_iter_conjugated_step` : Proves iteration-depth invariance under an involutive-conjugated step.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- None.

#### BUCKET 3: OPEN CLOSURE DEBT
- None.
-/
