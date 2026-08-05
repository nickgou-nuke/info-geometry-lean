import Mathlib.Tactic

def D4Lattice := Fin 4 → ℤ

def central_node_idx : Fin 4 := 1

def external_legs : List (Fin 4) := [0, 2, 3]

abbrev D4TrialityPerm :=
  {perm : Equiv.Perm (Fin 4) // perm central_node_idx = central_node_idx}

namespace D4TrialityPerm

abbrev perm (σ : D4TrialityPerm) : Equiv.Perm (Fin 4) := σ.1
abbrev fixes_central (σ : D4TrialityPerm) : σ.perm central_node_idx = central_node_idx := σ.2

end D4TrialityPerm

def D4Lattice.dot (v w : D4Lattice) : ℤ :=
  ∑ i : Fin 4, v i * w i

def apply_perm (σ : D4TrialityPerm) (v : D4Lattice) : D4Lattice :=
  fun i => v (σ.perm i)

theorem pin55_triality_invariant (σ : D4TrialityPerm) (v w : D4Lattice) :
    D4Lattice.dot (apply_perm σ v) (apply_perm σ w) = D4Lattice.dot v w := by
  dsimp [D4Lattice.dot, apply_perm]
  exact Equiv.sum_comp σ.perm (fun i => v i * w i)
