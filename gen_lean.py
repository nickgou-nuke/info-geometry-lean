def get_swap_lemmas(i, j):
    # Generates a lean tactic block to swap ι i and ι j
    pass

bivectors = [
    (0, 1, 3, 2, 3), # e0 e1 * e0 e1 e2 e3 -> e2 e3 (index 3)
    (0, 2, 4, 3, 1), # e0 e2 * e0 e1 e2 e3 -> e3 e1 (index 4)
    (0, 3, 5, 1, 2), # e0 e3 * e0 e1 e2 e3 -> e1 e2 (index 5)
    (2, 3, 0, 0, 1), # e2 e3 * e0 e1 e2 e3 -> e0 e1 (index 0)
    (3, 1, 1, 0, 2), # e3 e1 * e0 e1 e2 e3 -> e0 e2 (index 1)
    (1, 2, 2, 0, 3), # e1 e2 * e0 e1 e2 e3 -> e0 e3 (index 2)
]

def swap_str(a, b):
    return f"""
    have h_{a}_{b} : ι Q (gamma {a}) * ι Q (gamma {b}) = - (ι Q (gamma {b}) * ι Q (gamma {a})) := by
      apply ι_mul_ι_swap_of_orthogonal
      apply HasSpacetimeBasis.orthogonal
      decide
    rw [h_{a}_{b}]"""

out = ""
for case_idx, (b1, b2, target_idx, r1, r2) in enumerate(bivectors):
    out += f"  · -- case {case_idx}\n"
    out += f"    dsimp [basisBivector, gamma]\n"
    out += f"    rw [HasSpacetimeBasis.omega_eq (Q := Q)]\n"
    
    # We have ι b1 * ι b2 * (ι 0 * ι 1 * ι 2 * ι 3)
    # We want to move ι b1 and ι b2 next to their counterparts.
    # It's easier to just use a custom tactic or list the rw sequences.
    out += "    sorry\n"

print(out)
