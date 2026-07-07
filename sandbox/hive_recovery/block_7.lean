theorem wrappedRfl (n : Nat) : n = n := rfl

theorem passesByWrapper (n : Nat) : n = n :=
  wrappedRfl n

#enforce_non_triviality passesByWrapper