# FIBONACCI F-MATRIX AND R-MATRIX — SymPy

import sympy as sp

I = sp.I
pi = sp.pi

ONE = "1"
TAU = "τ"
CHANNELS = (ONE, TAU)


def fibonacci_FR(chirality=+1):
    """
    Return the nontrivial Fibonacci F-matrix and R-matrix.

    Basis order: [1, τ], meaning the intermediate fusion channel
    in τ ⊗ τ -> x, followed by x ⊗ τ -> τ.

    chirality = +1:
        R_1   = exp(+4πi/5)
        R_tau = exp(-3πi/5)

    chirality = -1:
        R_1   = exp(-4πi/5)
        R_tau = exp(+3πi/5)

    The two choices are complex conjugates.
    """

    phi = (1 + sp.sqrt(5)) / 2

    F = sp.Matrix([
        [1 / phi,          1 / sp.sqrt(phi)],
        [1 / sp.sqrt(phi), -1 / phi]
    ])

    R_1 = sp.exp(chirality * 4 * pi * I / 5)
    R_tau = sp.exp(-chirality * 3 * pi * I / 5)

    R = sp.diag(R_1, R_tau)

    R_symbols = {
        ONE: R_1,
        TAU: R_tau,
    }

    return phi, F, R, R_symbols


def max_abs_entry(M, digits=80):
    """Numerical max absolute entry of a SymPy matrix."""
    vals = [abs(complex(sp.N(x, digits))) for x in list(M)]
    return max(vals) if vals else 0.0


def check_zero(name, M, tol=1e-40):
    """Report whether a matrix is numerically zero."""
    err = max_abs_entry(M)
    status = "OK" if err < tol else "FAIL"
    print(f"{name:<45} max |entry| = {err:.3e}   {status}")
    return err


def right_hexagon_residual(F, R_symbols):
    """
    Component form of the Fibonacci right hexagon:

        R_c^{τ,τ} F[c,a] R_a^{τ,τ}
          =
        Σ_b F[c,b] R_τ^{τ,b} F[b,a]

    where a,b,c range over {1, τ}, and
        R_τ^{τ,1} = 1,
        R_τ^{τ,τ} = R_tau.
    """

    R_tau_b_to_tau = {
        ONE: sp.Integer(1),
        TAU: R_symbols[TAU],
    }

    residual = sp.zeros(2)

    for c, c_lab in enumerate(CHANNELS):
        for a, a_lab in enumerate(CHANNELS):
            lhs = R_symbols[c_lab] * F[c, a] * R_symbols[a_lab]
            rhs = sum(
                F[c, b] * R_tau_b_to_tau[b_lab] * F[b, a]
                for b, b_lab in enumerate(CHANNELS)
            )
            residual[c, a] = lhs - rhs

    return residual


def main(chirality=+1):
    phi, F, R, R_symbols = fibonacci_FR(chirality)

    I2 = sp.eye(2)

    # Braid generators on Hom(τ ⊗ τ ⊗ τ, τ).
    # σ1 braids the first two τ anyons.
    # σ2 braids the second two τ anyons.
    sigma1 = R
    sigma2 = F * R * F  # since F^{-1} = F in this gauge

    print("golden ratio φ:")
    print(phi)
    print()

    print("F matrix:")
    sp.pprint(F)
    print()

    print("R matrix:")
    sp.pprint(R)
    print()

    check_zero("F^2 - I", F * F - I2)
    check_zero("F†F - I", F.H * F - I2)
    check_zero("R†R - I", R.H * R - I2)

    H = right_hexagon_residual(F, R_symbols)
    check_zero("right hexagon residual", H)

    ybe = sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2
    check_zero("braid/YBE residual σ1σ2σ1 - σ2σ1σ2", ybe)

    print()
    print("σ1:")
    sp.pprint(sigma1)
    print()

    print("σ2 = F R F:")
    sp.pprint(sp.simplify(sigma2))

    return {
        "phi": phi,
        "F": F,
        "R": R,
        "sigma1": sigma1,
        "sigma2": sigma2,
        "hexagon_residual": H,
        "ybe_residual": ybe,
    }


if __name__ == "__main__":
    # Use chirality=-1 for the complex-conjugate convention.
    data = main(chirality=+1)
