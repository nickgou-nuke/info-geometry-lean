example (x y : Nat) : x = y -> y = x := by
  intro h
  exact h.symm
