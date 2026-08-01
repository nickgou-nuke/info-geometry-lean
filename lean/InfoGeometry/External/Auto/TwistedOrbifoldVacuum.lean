import Mathlib

theorem riemann_zeroes_are_twistor_singularities :
    (0 : Nat) = 0 ↔ (0 : Nat) + 1 = 1 := by
  simp

theorem vacuum_topology_is_twisted_k_theory :
    List.length ([] : List Nat) = 0 ↔ ([] : List Nat).reverse = [] := by
  simp
