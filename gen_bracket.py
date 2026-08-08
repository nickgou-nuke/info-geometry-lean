import re

def generate_commutator_proof():
    cases = []
    for i in range(6):
        for j in range(6):
            if i >= j:
                continue
            cases.append(f"  · -- case {i}, {j}\n    sorry")
    return "\n".join(cases)

print(generate_commutator_proof())
