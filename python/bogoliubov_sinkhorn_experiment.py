#!/usr/bin/env python3
"""
Numerical companion for the Bogoliubov–Sinkhorn Routing Bridge.

This script numerically demonstrates the pipeline:
  1. Create token states h_i
  2. Create expert-local linear maps B_e
  3. Compute compatibility cost C(i,e)
  4. Form Gibbs kernel K(i,e) = exp(-C(i,e) / ε)
  5. Sinkhorn-scale K to prescribed row/column marginals: P = diag(u) K diag(v)
  6. Compute h_out_i = Σ_e P(i,e) * B_e(h_i)
  7. Verify: row/column marginals, nonnegativity, subspace preservation

IMPORTANT: This is NOT proof authority. It is a numerical experiment only.
"""

import numpy as np
from typing import Tuple

np.random.seed(42)


def sinkhorn_scaling(
    K: np.ndarray,
    mu: np.ndarray,
    nu: np.ndarray,
    max_iter: int = 100,
    tol: float = 1e-10,
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Sinkhorn-Knopp scaling of kernel K to prescribed marginals mu, nu.

    Returns: (P, u, v) where P = diag(u) @ K @ diag(v)
    with row sums ≈ mu and column sums ≈ nu.
    """
    if K.ndim != 2 or K.shape[0] != K.shape[1]:
        raise ValueError("K must be a square matrix")
    if mu.shape != (K.shape[0],) or nu.shape != (K.shape[1],):
        raise ValueError("marginals must match the dimensions of K")
    if np.any(K < 0) or np.any(mu < 0) or np.any(nu < 0):
        raise ValueError("K and marginals must be nonnegative")
    if not np.all(np.isfinite(K)) or not np.all(np.isfinite(mu)) or not np.all(np.isfinite(nu)):
        raise ValueError("K and marginals must be finite")
    if np.any(K == 0):
        raise ValueError("K must be strictly positive for this scaling routine")
    if not np.isclose(mu.sum(), nu.sum()):
        raise ValueError("row and column marginals must have equal total mass")
    if max_iter <= 0 or tol <= 0:
        raise ValueError("max_iter and tol must be positive")

    n = K.shape[0]
    u = np.ones(n)
    v = np.ones(n)
    converged = False

    for _ in range(max_iter):
        # Row normalization
        Kv = K @ v
        u = mu / np.maximum(Kv, 1e-300)

        # Column normalization
        Ku = K.T @ u
        v = nu / np.maximum(Ku, 1e-300)

        # Check convergence
        P = np.diag(u) @ K @ np.diag(v)
        row_err = np.max(np.abs(P.sum(axis=1) - mu))
        col_err = np.max(np.abs(P.sum(axis=0) - nu))
        if row_err < tol and col_err < tol:
            converged = True
            break

    if not converged:
        raise RuntimeError("Sinkhorn scaling did not converge within max_iter")

    P = np.diag(u) @ K @ np.diag(v)
    return P, u, v


def run_experiment(n_tokens: int = 4, n_experts: int = 4, dim: int = 6, epsilon: float = 0.5):
    """
    Full Bogoliubov–Sinkhorn routing experiment.

    Parameters:
        n_tokens: Number of tokens
        n_experts: Number of experts
        dim: Dimension of latent space (doubled: dim/2 + dim/2)
        epsilon: Entropic regularization strength
    """
    if n_tokens != n_experts:
        raise ValueError("square coupling required for Birkhoff decomposition")
    if n_tokens <= 0:
        raise ValueError("at least one token and expert are required")
    if dim <= 0 or dim % 2 != 0:
        raise ValueError("dim must be a positive even dimension")
    if epsilon <= 0:
        raise ValueError("epsilon must be positive")
    n = n_tokens

    print(f"=" * 60)
    print(f"Bogoliubov–Sinkhorn Routing Numerical Experiment")
    print(f"n={n}, dim={dim}, ε={epsilon}")
    print(f"=" * 60)

    # 1. Create token states h_i (in the doubled space E ⊕ E)
    half = dim // 2
    h = np.random.randn(n, dim)
    print(f"\n[1] Token states: shape {h.shape}")

    # 2. Create expert-local linear maps B_e
    # These are general linear maps on the doubled space
    B = [np.random.randn(dim, dim) * 0.3 + np.eye(dim) for _ in range(n)]
    print(f"[2] Expert maps B_e: {n} matrices of shape ({dim},{dim})")

    # 3. Compute compatibility cost C(i,e) = ||h_i - B_e(h_i)||^2
    C = np.zeros((n, n))
    for i in range(n):
        for e in range(n):
            diff = h[i] - B[e] @ h[i]
            C[i, e] = np.dot(diff, diff)
    print(f"[3] Cost matrix C: shape {C.shape}")
    print(f"    C range: [{C.min():.4f}, {C.max():.4f}]")

    # 4. Form Gibbs kernel K(i,e) = exp(-C(i,e) / ε)
    K = np.exp(-C / epsilon)
    print(f"[4] Gibbs kernel K: shape {K.shape}")
    print(f"    K range: [{K.min():.6f}, {K.max():.6f}]")

    # 5. Sinkhorn scaling to uniform marginals
    mu = np.ones(n)  # uniform row marginals
    nu = np.ones(n)  # uniform column marginals
    P, u, v = sinkhorn_scaling(K, mu, nu)

    print(f"\n[5] Sinkhorn coupling P:")
    print(f"    P shape: {P.shape}")
    print(f"    P range: [{P.min():.6f}, {P.max():.6f}]")

    # 7. Verify properties
    print(f"\n[7] VERIFICATION:")

    # Nonnegativity
    nonneg = np.all(P >= -1e-12)
    print(f"    Nonnegativity:     {'PASS' if nonneg else 'FAIL'} (min P = {P.min():.2e})")

    # Row marginals
    row_sums = P.sum(axis=1)
    row_err = np.max(np.abs(row_sums - mu))
    print(f"    Row marginals:     {'PASS' if row_err < 1e-8 else 'FAIL'} (max error = {row_err:.2e})")

    # Column marginals
    col_sums = P.sum(axis=0)
    col_err = np.max(np.abs(col_sums - nu))
    print(f"    Column marginals:  {'PASS' if col_err < 1e-8 else 'FAIL'} (max error = {col_err:.2e})")

    # Bistochasticity (after normalizing to sum 1)
    is_bistochastic = row_err < 1e-8 and col_err < 1e-8 and nonneg
    print(f"    Bistochastic:      {'PASS' if is_bistochastic else 'FAIL'}")

    # 6. Compute h_out_i = Σ_e P(i,e) * B_e(h_i)
    h_out = np.zeros((n, dim))
    for i in range(n):
        for e in range(n):
            h_out[i] += P[i, e] * (B[e] @ h[i])

    print(f"\n[6] Balanced expert mixture h_out: shape {h_out.shape}")
    print(f"    h_out norms: {[f'{np.linalg.norm(h_out[i]):.4f}' for i in range(n)]}")

    # Subspace preservation test
    # Define U = {v : v's second half is zero} (i.e. base subspace)
    print(f"\n[SUBSPACE PRESERVATION TEST]")
    print(f"    U = {{v : v[{half}:] = 0}} (base subspace)")

    # Create inputs in U
    h_U = np.zeros((n, dim))
    h_U[:, :half] = np.random.randn(n, half)
    print(f"    Inputs in U: {np.allclose(h_U[:, half:], 0)}")

    # Create experts that preserve U: B_e maps U → U
    B_preserving = []
    for e in range(n):
        M = np.zeros((dim, dim))
        # Top-left block: maps first half to first half
        M[:half, :half] = np.random.randn(half, half) * 0.3 + np.eye(half)
        # Bottom-right block: maps second half to second half
        M[half:, half:] = np.random.randn(half, half) * 0.3 + np.eye(half)
        # No cross-terms: M[:half, half:] = 0 and M[half:, :half] = 0
        B_preserving.append(M)

    # Verify each expert preserves U
    for e in range(n):
        for i in range(n):
            out = B_preserving[e] @ h_U[i]
            assert np.allclose(out[half:], 0, atol=1e-12), f"Expert {e} does NOT preserve U on token {i}!"
    print(f"    All experts preserve U: True")

    # Compute cost with U-preserving experts
    C_U = np.zeros((n, n))
    for i in range(n):
        for e in range(n):
            diff = h_U[i] - B_preserving[e] @ h_U[i]
            C_U[i, e] = np.dot(diff, diff)

    K_U = np.exp(-C_U / epsilon)
    P_U, _, _ = sinkhorn_scaling(K_U, mu, nu)

    # Balanced output with U-preserving experts
    h_out_U = np.zeros((n, dim))
    for i in range(n):
        for e in range(n):
            h_out_U[i] += P_U[i, e] * (B_preserving[e] @ h_U[i])

    second_half_residual = np.max(np.abs(h_out_U[:, half:]))
    subspace_preserved = second_half_residual < 1e-10
    print(f"    Output in U:       {'PASS' if subspace_preserved else 'FAIL'} (max |v[{half}:]| = {second_half_residual:.2e})")

    # Load balance
    print(f"\n[LOAD BALANCE]")
    expert_loads = P.sum(axis=0)
    load_cv = np.std(expert_loads) / np.mean(expert_loads)
    print(f"    Expert loads: {[f'{l:.4f}' for l in expert_loads]}")
    print(f"    Load CV:      {load_cv:.6f}")

    # Operator-level warning
    print(f"\n[OPERATOR-LEVEL WARNING]")
    print(f"    The effective operator Σ_e P(i,e) B_e is a CONVEX combination of B_e.")
    print(f"    Even if each B_e is orthogonal/Bogoliubov, the mixture generally IS NOT.")
    B_eff = sum(P[0, e] * B[e] for e in range(n))
    I = np.eye(dim)
    orth_residual = np.linalg.norm(B_eff.T @ B_eff - I)
    print(f"    ||B_eff^T B_eff - I|| = {orth_residual:.4f}")
    print(f"    (This is NOT zero in general, confirming the mathematical warning.)")

    print(f"\n{'=' * 60}")
    print(f"SUMMARY:")
    print(f"  COMPUTED NUMERICALLY: All routing/mixture properties")
    print(f"  PROVED IN LEAN:      Submodule preservation")
    print(f"  NOT PROVED:          Operator-level group closure")
    print(f"  NOT CLAIMED:         Cl(5,5) preservation")
    print(f"{'=' * 60}")


if __name__ == "__main__":
    run_experiment()
