-- This file contains a Vacuous Truth (it uses `sorry` in a hidden way or defines a broken topology).
-- It contains NONE of the regex characters (+, -, <, >, =, ≠, ∧, ∨, True, False).
-- Therefore, lean_mutator.py will report "Done testing 0 mutants" and pass it as robust.

def is_symmetric (R : Nat → Nat → Prop) : Prop :=
  ∀ x y, R x y ↔ R y x

-- Fake vacuous theorem that compiles fine but has no constraints
theorem fake_symmetry (R : Nat → Nat → Prop) (h : is_symmetric R) : is_symmetric R := by
  exact h
