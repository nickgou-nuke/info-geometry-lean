import SelfReference.Core

/-!
# SelfReference.Counterexamples

Minimal examples separating closed-loop, reflective, and persistent capabilities.
-/

namespace SelfReference.Counterexamples

/-- 1. Closed-loop but not reflective.
    A simple incrementer that feeds back its output.
    It has no internal representation of its state.
-/
def incrementer : Agent where
  State := Nat
  Input := Nat
  Output := Nat
  step s i := (s + i, s + i)

/-- Closed-loop witness for `incrementer`. -/
def incrementerLoop : ClosedLoop incrementer where
  feed o := o

/-- 2. Reflective but not persistent.
    It can 'see' its state but cannot write to any memory that survives a step
    beyond the state transition itself.
-/
def mirror : Agent where
  State := Unit
  Input := Unit
  Output := Unit
  step _ _ := ((), ())

/-- Reflection witness for `mirror`. -/
def mirrorReflective : Reflective mirror where
  Rep := Unit
  reifyState _ := ()

/-- 3. Persistent but not self-modifying.
    A read-write memory that only changes when given an external input.
-/
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

end SelfReference.Counterexamples
