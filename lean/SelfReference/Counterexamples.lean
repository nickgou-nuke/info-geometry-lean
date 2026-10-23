/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import SelfReference.Memory

/-!
# SelfReference.Counterexamples

Concrete witnesses for the current agent interfaces. These examples do not
separate capabilities: the interfaces permit full-state reflection and memory
for every agent. Operational introspection and persistence across transitions
require additional specifications, not absence claims about these witnesses.
-/

namespace SelfReference.Counterexamples

/-- An incrementer whose output can be fed back as input. -/
def incrementer : Agent where
  State := Nat
  Input := Nat
  Output := Nat
  step s i := (s + i, s + i)

/-- Closed-loop witness for `incrementer`. -/
def incrementerLoop : ClosedLoop incrementer where
  feed o := o

/-- The one-state transition system. Both reflection and memory are available. -/
def mirror : Agent where
  State := Unit
  Input := Unit
  Output := Unit
  step _ _ := ((), ())

/-- Reflection witness for `mirror`. -/
def mirrorReflective : Reflective mirror where
  Rep := Unit
  reifyState _ := ()

/-- A memory cell: `none` preserves state and `some n` overwrites it. -/
def memoryCell : Agent where
  State := Nat
  Input := Option Nat
  Output := Nat
  step s i :=
    match i with
    | some n => (n, n)
    | none   => (s, s)

/-- Persistence witness for `memoryCell`. -/
def memoryCellPersistent : Persistent memoryCell where
  Memory := Nat
  read s := s
  write _ m := m

/-- The incrementer has faithful reflection under the actual interface. -/
example : Nonempty (FaithfulReflective incrementer) :=
  ⟨incrementer.stateReflection⟩

/-- Even the one-state system has lawful read/write memory. -/
example : Nonempty (InternalPersistent mirror) := ⟨mirror.stateMemory⟩

/-- No-input memory-cell updates preserve the stored value. -/
theorem memoryCell_idle (s : Nat) :
    (memoryCell.transitionRewrite none).rewrite s = s := rfl

/-- An explicit input overwrites the stored value. -/
theorem memoryCell_write (s n : Nat) :
    (memoryCell.transitionRewrite (some n)).rewrite s = n := rfl

end SelfReference.Counterexamples
