import sympy as sp


def verify_bender_hamiltonian():
    print("=== BENDER-BRODY-MULLER ZETA HAMILTONIAN: FINITE-SAFE SLICE ===")

    # Paper: H = S^{-1} (xp + px) S with S = 1 - exp(-i p).
    # The theorem-safe computable fragment is the commutative/classical shadow:
    # S^{-1}(xp+px)S = 2xp whenever S is invertible and x,p commute.
    x, p, S = sp.symbols("x p S", nonzero=True, commutative=True)

    core = x * p + p * x
    core_reduced = sp.simplify(core - 2 * x * p)
    assert core_reduced == 0

    H_classical = sp.simplify((1 / S) * core * S)
    assert sp.simplify(H_classical - 2 * x * p) == 0

    # Substitute the paper's formal factor after the abstract invertible-factor check.
    S_paper = 1 - sp.exp(-sp.I * p)
    H_paper_shadow = sp.simplify((1 / S_paper) * (2 * x * p) * S_paper)
    assert sp.simplify(H_paper_shadow - 2 * x * p) == 0

    # The eigenvalue/zero change of variables in the paper is algebraically inverse:
    # E = i(2z - 1), z = 1/2(1 - iE). This is not a zeta-zero proof.
    z, E = sp.symbols("z E")
    E_of_z = sp.I * (2 * z - 1)
    z_back = sp.Rational(1, 2) * (1 - sp.I * E_of_z)
    assert sp.simplify(z_back - z) == 0

    print(f"commutative_core = {sp.simplify(core)}")
    print(f"classical_similarity_shadow = {H_classical}")
    print(f"paper_factor_shadow = {H_paper_shadow}")
    print("eigenvalue_zero_affine_change_is_inverse = True")
    print("scope: finite commutative algebra only; no RH/self-adjointness/domain/zeta-zero proof")
    print("[SUCCESS] Bender-Brody-Muller finite-safe assertions passed")


if __name__ == '__main__':
    verify_bender_hamiltonian()
