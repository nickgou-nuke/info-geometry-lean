#!/usr/bin/env python3
"""Random walk on word prefix tree and Markov chain of thought on tensor tower."""

import numpy as np

# Vocabulary of the semantic space
VOCAB = ["quantum", "spin", "geometry", "spacetime", "colimit"]
PRIME_MAP = {w: p for w, p in zip(VOCAB, [2, 3, 5, 7, 11])}

# Attention Transition Matrix (Markov transition probabilities over Vocabulary)
# Transition probabilities from row word to column word
TRANSITION_PROBS = np.array([
    [0.1, 0.5, 0.3, 0.1, 0.0],  # quantum -> spin (0.5), geometry (0.3), etc.
    [0.1, 0.1, 0.5, 0.2, 0.1],  # spin -> geometry (0.5), spacetime (0.2)
    [0.0, 0.1, 0.1, 0.6, 0.2],  # geometry -> spacetime (0.6), colimit (0.2)
    [0.2, 0.0, 0.1, 0.1, 0.6],  # spacetime -> colimit (0.6)
    [0.5, 0.1, 0.1, 0.1, 0.2]   # colimit -> quantum (0.5)
])

# Pauli matrix basis for algebraic representation
SIGMA_Z = np.array([[1, 0], [0, -1]], dtype=complex)
SIGMA_X = np.array([[0, 1], [1, 0]], dtype=complex)

def word_to_operator(word):
    """Maps a word to a 2x2 complex operator using prime weight projection."""
    p = PRIME_MAP[word]
    # Represent as a linear combination in the local Clifford/Pauli space
    return (p * SIGMA_Z) + (1.0 / p * SIGMA_X)

def tensor_bond(op, n):
    """Bonding map: embeds an operator of stage n into stage n+1 (tensor identity)."""
    return np.kron(op, np.eye(2))

def run_random_walk(seed_word, steps=4):
    """Runs a random walk on the word prefix tree using Markov transitions."""
    current_word = seed_word
    chain = [current_word]
    
    print(f"   [Seed] {current_word}")
    for step in range(1, steps + 1):
        idx = VOCAB.index(current_word)
        probs = TRANSITION_PROBS[idx]
        # Sample next word using the Markov probabilities
        next_word = str(np.random.choice(VOCAB, p=probs))
        chain.append(next_word)
        print(f"   [Step {step}] {current_word} -> {next_word} (p={probs[VOCAB.index(next_word)]:.2f})")
        current_word = next_word
        
    return chain

def embed_chain_to_tower(chain):
    """Embeds the chain of thought into the inductive tensor tower."""
    # Stage 0
    op = word_to_operator(chain[0])
    print(f"\n   Stage 0: Operator shape {op.shape} for '{chain[0]}'")
    
    # Inductive stages
    for idx, word in enumerate(chain[1:], start=1):
        # Apply bonding map to project previous stage
        op_bonded = tensor_bond(op, idx - 1)
        # Tensor product with the new word operator
        op_new = word_to_operator(word)
        op = np.kron(op_bonded, op_new)
        print(f"   Stage {idx}: Operator shape {op.shape} (Bonded & Tense-multiplied with '{word}')")
        
    return op

def main():
    print("=== Word Prefix Tree Random Walk & Tensor Colimit Embeddings ===")
    
    # 1. Simulate the Chain of Thought via Random Walk
    print("\n1. Generating Chain of Thought via Markov Random Walk:")
    chain = run_random_walk("quantum", steps=4)
    print(f"   Generated Chain of Thought: {chain}")
    
    # 2. Embed the Chain into the Tensor Inductive Limit
    print("\n2. Projecting Chain onto Tensor Tower (Inductive Limit):")
    final_op = embed_chain_to_tower(chain)
    print(f"\n   Final Colimit Operator representation size: {final_op.shape}")
    print(f"   Trace of final operator: {np.trace(final_op)}")

if __name__ == "__main__":
    main()
