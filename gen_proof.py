import sys

basis = [
    [0, 1],
    [0, 2],
    [0, 3],
    [2, 3],
    [3, 1],
    [1, 2]
]

omega = [0, 1, 2, 3]

def sign_and_result(b):
    # multiply b * omega
    # return sign, bivector index
    # We'll just generate sorry for now to avoid complexity in this mock example
    pass

proof = """
lemma basisBivector_mul_omega (i : Fin 6) : 
    basisBivector Q i * Omega (Q := Q) ∈ Bivector13 Q := by
  fin_cases i
"""
for i in range(6):
    proof += f"  · -- case {i}\n    sorry\n"

with open("proof_out.lean", "w") as f:
    f.write(proof)
