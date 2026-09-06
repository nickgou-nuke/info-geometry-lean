import SelfReference.Core

/-!
# SelfReference.Dynamics

Basic iteration and invariance lemmas for closed-loop agent dynamics.
-/

namespace SelfReference

universe u

/--
  The fundamental theorem of recursive dynamics:
  n+m steps is equivalent to n steps followed by m steps.
-/
theorem iterate_add (A : Agent.{u}) (L : ClosedLoop A) (n m : Nat) (x : A.State × A.Input) :
    iterateClosedLoop A L (n + m) x = iterateClosedLoop A L n (iterateClosedLoop A L m x) := by
  induction n with
  | zero =>
      simp [iterateClosedLoop]
  | succ n ih =>
      simp [iterateClosedLoop, Nat.succ_add, ih]

/--
  The state trajectory induced by the closed-loop feedback.
-/
def trajectory (A : Agent.{u}) (L : ClosedLoop A) (s0 : A.State) (i0 : A.Input) :
    Nat → A.State × A.Input
  | n => iterateClosedLoop A L n (s0, i0)

/--
  Invariance: If a state-input pair is a fixed point of the loop,
  the trajectory remains constant.
-/
theorem trajectory_fixed_point (A : Agent.{u}) (L : ClosedLoop A) (s : A.State) (i : A.Input) :
    loopStep A L (s, i) = (s, i) → ∀ n, iterateClosedLoop A L n (s, i) = (s, i) := by
  intro h_fixed n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [iterateClosedLoop]
    rw [ih]
    exact h_fixed

end SelfReference
