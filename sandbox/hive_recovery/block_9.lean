import Lean

open InfoGeometry.Lint

theorem trivialEq (n : Nat) : n = n := rfl
#audit_non_triviality trivialEq
-- should warn/fail

theorem localHyp (P : Prop) (h : P) : P := h
#audit_non_triviality localHyp
-- should warn/fail

theorem wrappedRfl (n : Nat) : n = n := rfl

theorem passesByWrapper (n : Nat) : n = n :=
  wrappedRfl n

#audit_non_triviality passesByWrapper
-- should warn/fail if `wrappedRfl` is under `InfoGeometry`

theorem addCommExample (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

#audit_non_triviality addCommExample
-- should pass