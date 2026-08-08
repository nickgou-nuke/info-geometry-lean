import sys
from pathlib import Path

def generate_full_oracle_prompt():
    colimit_code = Path("/home/goutev/auto/proofs/InfinityFilteredColimits.lean").read_text()
    fib_code = Path("/home/goutev/auto/proofs/FibAnyonThm6_pentagon.lean").read_text()

    prompt = f"""You are the Intuition Oracle for an Automath pipeline.
Your job is to propose a rigorous mathematical hypothesis and its Lean 4 implementation.
Do not hallucinate external dependencies. You must strictly align with the provided causal cone.

=== CAUSAL CONE (EXACT SOURCE CONTEXT) ===

--- InfinityFilteredColimits.lean ---
{colimit_code}

--- FibAnyonThm6_pentagon.lean ---
{fib_code}

=== YOUR GOAL ===
The current FibAnyonThm6_pentagon.lean defines the Fibonacci F-matrix algebraically but explicitly notes it does not formalize a full monoidal category.
Formulate the true Pentagon Identity (Mac Lane coherence) for Fibonacci Anyons within the existing Filtered Colimit structure provided above.

Provide only the valid Lean 4 code to implement this hypothesis. The pipeline will test your code natively.
"""
    return prompt

if __name__ == "__main__":
    print(generate_full_oracle_prompt())
