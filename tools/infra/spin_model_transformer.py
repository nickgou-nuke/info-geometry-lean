#!/usr/bin/env python3
"""Spin-Model Transformer: Mean-Field & TAP / Plefka corrections."""

import numpy as np

def softmax(x, axis=-1):
    exps = np.exp(x - np.max(x, axis=axis, keepdims=True))
    return exps / np.sum(exps, axis=axis, keepdims=True)

class SpinModelTransformer:
    def __init__(self, d_model, num_tokens, beta=1.0):
        self.d = d_model
        self.n = num_tokens
        self.beta = beta
        # Initialize query, key, value projections
        self.W_Q = np.random.randn(self.d, self.d) / np.sqrt(self.d)
        self.W_K = np.random.randn(self.d, self.d) / np.sqrt(self.d)
        self.W_V = np.random.randn(self.d, self.d) / np.sqrt(self.d)
        # Feed-forward weights (to simulate the TAP correction map)
        self.W_1 = np.random.randn(2 * self.d, self.d) / np.sqrt(self.d)
        self.W_2 = np.random.randn(self.d, 2 * self.d) / np.sqrt(2 * self.d)

    def mean_field_attention(self, M):
        """Standard first-order mean-field update (similar to self-attention)."""
        Q = M @ self.W_Q.T
        K = M @ self.W_K.T
        V = M @ self.W_V.T
        
        # Attention scores J_ij
        scores = (Q @ K.T) / np.sqrt(self.d)
        J = softmax(scores, axis=-1)
        
        # Mean field local field
        B_att = J @ V
        return B_att

    def tap_correction(self, M, J):
        """Second-order Plefka / Thouless-Anderson-Palmer correction.
        FFN layers act as parameter-rich approximations to the reaction field
        which corrects the self-polarization of the spins.
        """
        # Onsager reaction field: corrects the bias from a spin's own contribution
        # to the local field of its neighbors.
        # Delta B_i = - beta * sum_j J_ij^2 (1 - ||m_j||^2) m_i
        norms_sq = np.sum(M ** 2, axis=-1, keepdims=True)  # (n, 1)
        susceptibility = 1.0 - norms_sq  # (n, 1)
        
        # J_ij squared term
        J_sq = J ** 2
        
        # Compute local correction term
        reaction_coeff = self.beta * (J_sq @ susceptibility)  # (n, 1)
        B_tap = - reaction_coeff * M  # (n, d)
        
        # Simulate neural-network FFN response (approximation of the non-linear TAP correction)
        # FFN(x) = Relu(x W1) W2
        FFN_out = np.maximum(0, M @ self.W_1.T) @ self.W_2.T
        
        return B_tap, FFN_out

    def forward_step(self, x):
        """Performs a forward step simulating the spin relaxation."""
        M = x.copy()
        print(f"   Initial token norms: {np.linalg.norm(M, axis=-1)}")
        
        # Mean-field step (Self-Attention)
        Q = M @ self.W_Q.T
        K = M @ self.W_K.T
        scores = (Q @ K.T) / np.sqrt(self.d)
        J = softmax(scores, axis=-1)
        B_att = J @ (M @ self.W_V.T)
        
        # Compute explicit physics-based TAP correction and the FFN emulator
        B_tap, FFN_out = self.tap_correction(M, J)
        
        # Final state updating
        M_new_phys = M + B_att + B_tap
        M_new_nn = M + B_att + FFN_out
        
        print(f"   Mean-field field norm: {np.linalg.norm(B_att, axis=-1)}")
        print(f"   TAP reaction field norm: {np.linalg.norm(B_tap, axis=-1)}")
        print(f"   FFN output norm: {np.linalg.norm(FFN_out, axis=-1)}")
        return M_new_phys, M_new_nn

def main():
    print("=== Spin-Model Transformer: Mean-Field & TAP Corrections ===")
    np.random.seed(42)
    model = SpinModelTransformer(d_model=4, num_tokens=3, beta=0.8)
    
    # 3 tokens (e.g. quantum, spin, geometry)
    x = np.random.randn(3, 4)
    # Project to unit sphere to represent spins
    x /= np.linalg.norm(x, axis=-1, keepdims=True)
    
    M_phys, M_nn = model.forward_step(x)
    print("\n   Spins updated under physical TAP model:")
    print(M_phys)
    print("\n   Spins updated under neural FFN model:")
    print(M_nn)

if __name__ == "__main__":
    main()
