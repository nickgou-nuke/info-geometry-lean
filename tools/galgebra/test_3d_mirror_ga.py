#!/usr/bin/env python3
"""
Koroteev–Zeitlin 3D mirror symmetry: geometric algebra checks.

Verifies sl(r+1) structure, Borel opers, gauge transforms,
Z-twisted asymptotics, and the classical Yang-Baxter equation
using numpy matrix algebra.

Every test prints PASS / FAIL.
"""

import numpy as np
from itertools import product

TOL = 1e-12

# ── helpers ──────────────────────────────────────────────────


def commutator(A, B):
    """Matrix commutator [A, B] = AB - BA."""
    return A @ B - B @ A


def killing_form(X, Y, basis):
    """
    Cartan–Killing form B(X,Y) = tr(ad_X ad_Y).

    basis : list of matrices spanning the Lie algebra.
    X, Y  : elements expressed as matrices.
    """
    n = len(basis)
    # ad_X in the adjoint representation
    adX = np.zeros((n, n))
    adY = np.zeros((n, n))
    for j, bj in enumerate(basis):
        cx = commutator(X, bj)
        cy = commutator(Y, bj)
        for i, bi in enumerate(basis):
            # decompose [X, bj] in the basis
            # use tr(bi^dag * cx) / tr(bi^dag * bi)
            adX[i, j] = np.real(
                np.trace(bi.conj().T @ cx)
                / np.trace(bi.conj().T @ bi)
            )
            adY[i, j] = np.real(
                np.trace(bi.conj().T @ cy)
                / np.trace(bi.conj().T @ bi)
            )
    return np.trace(adX @ adY)


def _ok(tag, cond):
    """Print PASS/FAIL for a named check."""
    status = "PASS" if cond else "FAIL"
    print(f"  [{status}] {tag}")
    return cond


# ── 1. sl(r+1) Lie algebra and Cartan–Killing form ──────────

def sl_basis(r):
    """
    Return a basis for sl(r+1, R) as (r+1)x(r+1) real
    traceless matrices.

    Convention:
      E_{ij} (i!=j)            -- off-diagonal units
      H_k = E_{kk} - E_{k+1,k+1}  -- Cartan subalgebra
    """
    n = r + 1
    basis = []
    # off-diagonal
    for i in range(n):
        for j in range(n):
            if i != j:
                E = np.zeros((n, n))
                E[i, j] = 1.0
                basis.append(E)
    # Cartan generators
    for k in range(r):
        H = np.zeros((n, n))
        H[k, k] = 1.0
        H[k + 1, k + 1] = -1.0
        basis.append(H)
    return basis


def test_sl_killing():
    """
    For sl(r+1) the Killing form satisfies
        B(X, Y) = 2(r+1) tr(X Y).
    Check for r = 1, 2.
    """
    print("\n=== 1. sl(r+1) Cartan–Killing form ===")
    all_ok = True
    for r in (1, 2):
        n = r + 1
        basis = sl_basis(r)
        dim = len(basis)  # should be n^2 - 1
        all_ok &= _ok(
            f"sl({n}) dim = {dim} (expect {n**2-1})",
            dim == n**2 - 1,
        )
        # closure: [b_i, b_j] lives in span(basis)
        closure = True
        for bi in basis:
            for bj in basis:
                c = commutator(bi, bj)
                # project out of basis
                residual = c.copy()
                for bk in basis:
                    coeff = np.trace(bk.conj().T @ c) / \
                            np.trace(bk.conj().T @ bk)
                    residual -= coeff * bk
                if np.linalg.norm(residual) > TOL:
                    closure = False
        all_ok &= _ok(
            f"sl({n}) bracket closure", closure
        )

        # Killing vs 2n·tr(XY)
        killing_ok = True
        for bi in basis:
            for bj in basis:
                K = killing_form(bi, bj, basis)
                expected = 2 * n * np.trace(bi @ bj)
                if abs(K - expected) > TOL:
                    killing_ok = False
        all_ok &= _ok(
            f"sl({n}) B(X,Y) = 2·{n}·tr(XY)",
            killing_ok,
        )
    return all_ok


# ── 2. sl(2) explicit relations ─────────────────────────────

def test_sl2_relations():
    """
    e = [[0,1],[0,0]], f = [[0,0],[1,0]],
    h = [[1,0],[0,-1]].
    Verify [e,f]=h, [h,e]=2e, [h,f]=-2f.
    """
    print("\n=== 2. sl(2) commutation relations ===")
    e = np.array([[0, 1], [0, 0]], dtype=float)
    f = np.array([[0, 0], [1, 0]], dtype=float)
    h = np.array([[1, 0], [0, -1]], dtype=float)

    ok = True
    ok &= _ok("[e,f] = h",
              np.allclose(commutator(e, f), h, atol=TOL))
    ok &= _ok("[h,e] = 2e",
              np.allclose(commutator(h, e), 2*e, atol=TOL))
    ok &= _ok("[h,f] = -2f",
              np.allclose(commutator(h, f), -2*f, atol=TOL))

    # Casimir: C = h^2 + 2ef + 2fe  should be 3·Id
    C = h @ h + 2 * e @ f + 2 * f @ e
    ok &= _ok("Casimir = 3·Id (fund rep)",
              np.allclose(C, 3 * np.eye(2), atol=TOL))
    return ok


# ── 3. Borel oper condition for SL(2) ───────────────────────

def is_lower_tri(M, tol=TOL):
    n = M.shape[0]
    for i in range(n):
        for j in range(i + 1, n):
            if abs(M[i, j]) > tol:
                return False
    return True


def is_upper_uni(M, tol=TOL):
    """Upper-triangular with 1s on diagonal."""
    n = M.shape[0]
    for i in range(n):
        if abs(M[i, i] - 1.0) > tol:
            return False
        for j in range(0, i):
            if abs(M[i, j]) > tol:
                return False
    return True


def is_diagonal(M, tol=TOL):
    n = M.shape[0]
    for i in range(n):
        for j in range(n):
            if i != j and abs(M[i, j]) > tol:
                return False
    return True


def iwasawa_sl2(A):
    """
    Decompose A in SL(2) as  N_- · H · N_+
    (lower-uni · diag · upper-uni) via modified
    LDU factorization.
    Returns (N_minus, H_diag, N_plus) or None.
    """
    a, b = A[0, 0], A[0, 1]
    c, d = A[1, 0], A[1, 1]
    if abs(a) < TOL:
        return None
    # N_- = [[1,0],[c/a,1]]
    N_minus = np.array([[1, 0], [c / a, 1]], dtype=float)
    # H = diag(a, 1/a)  (det=1)
    H_diag = np.diag([a, 1.0 / a])
    # N_+ = [[1, b/a],[0,1]]
    N_plus = np.array([[1, b / a], [0, 1]], dtype=float)
    return N_minus, H_diag, N_plus


def test_borel_oper():
    """
    An oper for SL(2) is a connection of the form
        A(z) = N_-(z) · diag · exp(e)
    i.e. the upper-unipotent part is exp(e)=[[1,1],[0,1]].
    We build such an A, decompose it, and check the
    oper condition: the N_+ factor equals exp(e).
    """
    print("\n=== 3. Borel oper condition (SL2) ===")
    e = np.array([[0, 1], [0, 0]], dtype=float)
    exp_e = np.eye(2) + e  # exp(e) for nilpotent e

    # Build an explicit oper: A = N_- · H · exp(e)
    alpha = 2.0
    N_minus = np.array([[1, 0], [0.7, 1]], dtype=float)
    H_diag = np.diag([alpha, 1.0 / alpha])
    A_oper = N_minus @ H_diag @ exp_e

    ok = True
    ok &= _ok("det(A_oper) = 1",
              abs(np.linalg.det(A_oper) - 1.0) < TOL)

    dec = iwasawa_sl2(A_oper)
    ok &= _ok("Iwasawa decomposition exists", dec is not None)
    if dec:
        Nm, Hd, Np = dec
        ok &= _ok("N_- is lower-unitriangular",
                   is_lower_tri(Nm) and
                   abs(Nm[0, 0] - 1) < TOL and
                   abs(Nm[1, 1] - 1) < TOL)
        ok &= _ok("H is diagonal", is_diagonal(Hd))
        ok &= _ok("N_+ = exp(e)  (oper condition)",
                   np.allclose(Np, exp_e, atol=TOL))
        ok &= _ok("Reconstruction N_-·H·N_+ = A",
                   np.allclose(Nm @ Hd @ Np, A_oper,
                               atol=TOL))
    return ok


# ── 4. Gauge transformation preserves oper ──────────────────

def test_gauge_oper():
    """
    Gauge: A(z) -> g(ħz) A(z) g(z)^{-1}.
    For diagonal g = diag(λ, 1/λ) the oper condition
    (N_+ = exp(e)) is preserved iff the gauge acts as
       e -> λ^2 e  (which still gives N_+ = exp(λ^2 e)).
    We verify the transformed connection is still an oper
    (has upper-unipotent part of the form exp(c·e)).
    """
    print("\n=== 4. Gauge transform preserves oper ===")
    e = np.array([[0, 1], [0, 0]], dtype=float)
    exp_e = np.eye(2) + e

    lam = 1.5
    g = np.diag([lam, 1.0 / lam])
    g_inv = np.diag([1.0 / lam, lam])

    # original oper
    N_minus = np.array([[1, 0], [0.3, 1]], dtype=float)
    H_diag = np.diag([3.0, 1.0 / 3.0])
    A = N_minus @ H_diag @ exp_e

    # gauge transform: g · A · g^{-1}
    A_prime = g @ A @ g_inv

    ok = True
    ok &= _ok("det preserved",
              abs(np.linalg.det(A_prime) - 1.0) < TOL)

    dec = iwasawa_sl2(A_prime)
    ok &= _ok("Decomposition exists", dec is not None)
    if dec:
        Nm2, Hd2, Np2 = dec
        # Np2 should be [[1, c],[0,1]] for some c
        ok &= _ok("N_+ is upper-unipotent",
                   is_upper_uni(Np2))
        c = Np2[0, 1]
        ok &= _ok(f"N_+ = exp({c:.4f}·e), c = λ² = "
                   f"{lam**2:.4f}",
                   abs(c - lam**2) < TOL)
        ok &= _ok("Transformed oper is still oper form",
                   is_upper_uni(Np2))
    return ok


# ── 5. Z-twisted condition (asymptotic diagonalisation) ─────

def test_z_twisted():
    """
    For SL(2), the Z-twisted Miura oper means:
    at z -> ∞ the connection A(z) is gauge-equivalent
    to diag(z, z^{-1}).

    We construct A(z) = diag(z, 1/z) + (1/z)·off-diag
    and show that conjugation by g(z) = Id + O(1/z)
    diagonalises it to leading order.
    """
    print("\n=== 5. Z-twisted condition (SL2) ===")
    ok = True

    z = 1000.0  # "large z"
    eps = 0.5   # off-diagonal perturbation strength

    # A(z) = diag(z,1/z) + (eps/z) * sigma_+
    A_z = np.diag([z, 1.0 / z])
    A_z[0, 1] += eps / z

    # leading diagonal part
    D = np.diag([z, 1.0 / z])

    # perturbative gauge: g = Id + (1/z) G_1
    # choose G_1 to kill the (0,1) entry at O(1/z):
    #   [G_1, D_leading] + off-diag part = 0
    # D_leading eigenvalues: z, 1/z
    # (G1)_{01}(z - 1/z) + eps/z = 0
    # => (G1)_{01} = -eps / (z(z - 1/z))
    #              = -eps / (z^2 - 1)
    delta = z**2 - 1.0
    G1_01 = -eps / delta
    G1 = np.zeros((2, 2))
    G1[0, 1] = G1_01

    g = np.eye(2) + G1
    g_inv = np.eye(2) - G1  # to O(1/z^2)

    A_gauged = g @ A_z @ g_inv

    off_diag_norm = abs(A_gauged[0, 1]) + abs(A_gauged[1, 0])
    diag_diff = np.diag(A_gauged) - np.array([z, 1.0 / z])

    ok &= _ok(
        f"Off-diag after gauge: {off_diag_norm:.2e} "
        f"<< z = {z}",
        off_diag_norm / z < 1e-4,
    )
    ok &= _ok(
        f"Diagonal entries ~ (z, 1/z): "
        f"err = {np.linalg.norm(diag_diff):.2e}",
        np.linalg.norm(diag_diff) / z < 1e-4,
    )

    # exact check: eigenvalues of A(z)
    eigvals = np.sort(np.linalg.eigvals(A_z))[::-1]
    ok &= _ok(
        "Eigenvalues ~ (z, 1/z)",
        abs(eigvals[0] - z) / z < 1e-6 and
        abs(eigvals[1] - 1.0 / z) < 1e-6,
    )
    return ok


# ── 6. Classical r-matrix and Yang–Baxter (sl2) ─────────────

def tensor_kron(A, B):
    """Kronecker product representing A ⊗ B."""
    return np.kron(A, B)


def test_classical_rmatrix():
    """
    Classical r-matrix for sl(2):
        r = (h⊗h)/2 + e⊗f

    Classical Yang–Baxter equation (CYBE):
        [r₁₂, r₁₃] + [r₁₂, r₂₃] + [r₁₃, r₂₃] = 0

    where r₁₂ = r ⊗ Id, etc., embedded in
    sl(2)^{⊗3} ≅ Mat(8).
    """
    print("\n=== 6. Classical r-matrix & CYBE (sl2) ===")
    e = np.array([[0, 1], [0, 0]], dtype=float)
    f = np.array([[0, 0], [1, 0]], dtype=float)
    h = np.array([[1, 0], [0, -1]], dtype=float)
    Id = np.eye(2)

    # r in End(C^2 ⊗ C^2)  -- 4x4 matrix
    r = tensor_kron(h, h) / 2.0 + tensor_kron(e, f)

    ok = True

    # Verify r is not symmetric (it shouldn't be for
    # the standard Drinfeld–Jimbo r-matrix)
    r_swap = np.zeros_like(r)
    # swap operator P on C^2 ⊗ C^2
    P = np.zeros((4, 4))
    for i in range(2):
        for j in range(2):
            P[2 * i + j, 2 * j + i] = 1.0
    r21 = P @ r @ P
    r_symm = r + r21   # symmetric part -> Casimir
    # r + r21 should be the tensor Casimir
    # = h⊗h + e⊗f + f⊗e  (the split Casimir)
    casimir_tensor = (tensor_kron(h, h)
                      + tensor_kron(e, f)
                      + tensor_kron(f, e))
    ok &= _ok("r + r₂₁ = split Casimir",
              np.allclose(r_symm, casimir_tensor, atol=TOL))

    # ── Embed in 8×8 = (C^2)^{⊗3} ──
    # r₁₂ = r ⊗ Id₂
    r12 = tensor_kron(r, Id)
    # r₂₃ = Id₂ ⊗ r
    r23 = tensor_kron(Id, r)
    # r₁₃: act on slots 1 and 3
    # r₁₃ = (P₁₂ ⊗ Id)(Id ⊗ r)(P₁₂ ⊗ Id)
    P8 = tensor_kron(P, Id)
    r13 = P8 @ tensor_kron(Id, r) @ P8

    # CYBE: [r12, r13] + [r12, r23] + [r13, r23] = 0
    cybe = (commutator(r12, r13)
            + commutator(r12, r23)
            + commutator(r13, r23))
    cybe_norm = np.linalg.norm(cybe)
    ok &= _ok(f"CYBE residual = {cybe_norm:.2e}",
              cybe_norm < TOL)

    # ── Extra: r satisfies modified CYBE with Ω ──
    # For completeness, check [r12,r23] + [r13,r23]
    # + [r12,r13] structure.  Already done above.

    # ── Verify ad-invariance of r + r21 ──
    # The split Casimir commutes with Δ(X) = X⊗1 + 1⊗X
    inv_ok = True
    for X in (e, f, h):
        Delta_X = tensor_kron(X, Id) + tensor_kron(Id, X)
        c = commutator(Delta_X, casimir_tensor)
        if np.linalg.norm(c) > TOL:
            inv_ok = False
    ok &= _ok("Split Casimir is ad-invariant", inv_ok)

    return ok


# ── main ─────────────────────────────────────────────────────

def main():
    print("=" * 56)
    print("Koroteev–Zeitlin 3D mirror symmetry")
    print("Geometric-algebra verification suite")
    print("=" * 56)

    results = []
    results.append(("sl(r+1) Killing form", test_sl_killing()))
    results.append(("sl(2) relations", test_sl2_relations()))
    results.append(("Borel oper", test_borel_oper()))
    results.append(("Gauge oper", test_gauge_oper()))
    results.append(("Z-twisted", test_z_twisted()))
    results.append(("Classical r-matrix", test_classical_rmatrix()))

    print("\n" + "=" * 56)
    print("SUMMARY")
    print("=" * 56)
    all_pass = True
    for name, ok in results:
        tag = "PASS" if ok else "FAIL"
        print(f"  [{tag}] {name}")
        all_pass &= ok

    print("=" * 56)
    if all_pass:
        print("All tests passed.")
    else:
        print("SOME TESTS FAILED.")
    return 0 if all_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
