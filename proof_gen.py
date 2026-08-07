def generate_proof():
    code = """
lemma basisBivector_mul_omega (i : Fin 6) : 
    basisBivector Q i * Omega (Q := Q) ∈ Bivector13 Q := by
  revert i
  intro i
  fin_cases i
"""
    # Define the 6 cases manually
    # 0: 01 * 0123 -> -Q0 Q1 23
    # 1: 02 * 0123 -> Q0 Q2 13 = -Q0 Q2 31 (wait, basis 4 is 31, basis 5 is 12)
    # let's just write the exact sequence of rw for each case!

    # A python script to find the sequence of transpositions
    def get_swaps(a, b):
        return f"    -- need to swap {a} and {b}\n"

    # Actually, generating Lean tactic steps is easy:
    # We want to reduce `(a*b) * (0*1*2*3)`.
    pass
