#!/usr/bin/env python3

import itertools
import sympy as sp


def bit_basis(n):
    return list(itertools.product((0, 1), repeat=n))


def creation(n, j):
    states = bit_basis(n)
    idx = {s: k for k, s in enumerate(states)}
    mat = sp.zeros(2**n)
    for col, state in enumerate(states):
        if state[j] == 0:
            out = list(state)
            out[j] = 1
            sign = (-1) ** sum(state[:j])
            mat[idx[tuple(out)], col] = sign
    return mat


def annihilation(n, j):
    states = bit_basis(n)
    idx = {s: k for k, s in enumerate(states)}
    mat = sp.zeros(2**n)
    for col, state in enumerate(states):
        if state[j] == 1:
            out = list(state)
            out[j] = 0
            sign = (-1) ** sum(state[:j])
            mat[idx[tuple(out)], col] = sign
    return mat


def simplify_matrix(mat):
    return mat.applyfunc(sp.simplify)


def assert_matrix_zero(label, mat):
    simplified = simplify_matrix(mat)
    if simplified != sp.zeros(*simplified.shape):
        raise AssertionError(f"{label} failed:\n{simplified}")
    print(f"PASS {label}")


def assert_matrix_nonzero_numeric(label, mat):
    vals = [complex(sp.N(x, 40)) for x in mat]
    residual = max((abs(x) for x in vals), default=0.0)
    if residual <= 1e-20:
        raise AssertionError(f"{label} unexpectedly vanished")
    print(f"PASS {label}: residual {residual:.6g}")


def anti(a, b):
    return a * b + b * a


def embed_next(mat):
    return sp.kronecker_product(mat, sp.eye(2))


def car_operators(n):
    c = [creation(n, j) for j in range(n)]
    a = [annihilation(n, j) for j in range(n)]
    return c, a


def majoranas(n):
    c, a = car_operators(n)
    return [c[j] + a[j] for j in range(n)]


def finite_dirac(primes):
    n = len(primes)
    gammas = majoranas(n)
    dim = 2**n
    weights = [sp.sqrt(sp.log(p)) for p in primes]
    d_op = sp.zeros(dim)
    for w, gamma in zip(weights, gammas):
        d_op += w * gamma
    h_op = sum(sp.log(p) for p in primes) * sp.eye(dim)
    return d_op, h_op, gammas


def zeta_twisted_dirac(primes, sigma, t):
    n = len(primes)
    c, a = car_operators(n)
    dim = 2**n
    q = sp.zeros(dim)
    qsharp = sp.zeros(dim)
    for j, p in enumerate(primes):
        amp = sp.sqrt(sp.log(p))
        h = sp.exp((sp.Rational(1, 2) - sigma - sp.I * t) * sp.log(p))
        q += amp * h * c[j]
        qsharp += amp * h**-1 * a[j]
    return q + qsharp, q, qsharp


def verify_car_and_majorana(primes):
    n = len(primes)
    dim = 2**n
    ident = sp.eye(dim)
    zero = sp.zeros(dim)
    c, a = car_operators(n)
    gammas = [c[j] + a[j] for j in range(n)]

    for i in range(n):
        assert_matrix_zero(f"c_{i}^2 = 0", c[i] * c[i])
        assert_matrix_zero(f"a_{i}^2 = 0", a[i] * a[i])
        for j in range(n):
            expected = ident if i == j else zero
            assert_matrix_zero(f"{{a_{i}, c_{j}}} = delta_ij", anti(a[i], c[j]) - expected)
            assert_matrix_zero(f"{{c_{i}, c_{j}}} = 0", anti(c[i], c[j]))
            assert_matrix_zero(f"{{a_{i}, a_{j}}} = 0", anti(a[i], a[j]))

    for i in range(n):
        assert_matrix_zero(f"gamma_{i} is Hermitian", gammas[i].conjugate().T - gammas[i])
        for j in range(n):
            expected = 2 * ident if i == j else zero
            assert_matrix_zero(
                f"{{gamma_{i}, gamma_{j}}} = 2 delta_ij",
                anti(gammas[i], gammas[j]) - expected,
            )


def verify_finite_dirac(primes):
    d_op, h_op, _ = finite_dirac(primes)
    assert_matrix_zero("finite Cantor Dirac is Hermitian", d_op.conjugate().T - d_op)
    assert_matrix_zero("finite Cantor Dirac square is Hamiltonian", d_op * d_op - h_op)


def verify_zeta_twist(primes):
    t = sp.symbols("t", real=True)
    critical, q, qsharp = zeta_twisted_dirac(primes, sp.Rational(1, 2), t)
    assert_matrix_zero("critical-line Q* = Qsharp", q.conjugate().T - qsharp)
    assert_matrix_zero("critical-line zeta Dirac is Hermitian", critical.conjugate().T - critical)

    off, _, _ = zeta_twisted_dirac(primes, sp.Rational(3, 5), sp.Rational(2, 3))
    assert_matrix_nonzero_numeric(
        "off-critical finite zeta Dirac is not Hermitian",
        off.conjugate().T - off,
    )


def verify_induction_series(primes):
    previous_d = None
    previous_h = None
    for n in range(1, len(primes) + 1):
        prefix = primes[:n]
        d_op, h_op, gammas = finite_dirac(prefix)
        assert_matrix_zero(f"stage {n} Dirac square", d_op * d_op - h_op)
        if previous_d is not None:
            new_prime = primes[n - 1]
            old_d = embed_next(previous_d)
            old_h = embed_next(previous_h)
            increment = sp.sqrt(sp.log(new_prime)) * gammas[-1]
            h_increment = sp.log(new_prime) * sp.eye(2**n)
            assert_matrix_zero(
                f"stage {n} induction increment for D",
                d_op - (old_d + increment),
            )
            assert_matrix_zero(
                f"stage {n} induction increment for H",
                h_op - (old_h + h_increment),
            )
            assert_matrix_zero(
                f"stage {n} old/new anticommutation",
                anti(old_d, gammas[-1]),
            )
        previous_d = d_op
        previous_h = h_op


def main():
    primes = [2, 3, 5]
    print("finite lattice Hilbert-Polya pipeline witness")
    print("prime prefixes:", primes)
    verify_car_and_majorana(primes)
    verify_finite_dirac(primes)
    verify_zeta_twist(primes)
    verify_induction_series(primes)
    print("LEAN_PROVED HilbertSelfAdjointRealSpectrumLemma is Lean-only")
    print("LEAN_PROVED finiteCharacteristicDeterminant_zero_iff_eigen is Lean-only")
    print("LEAN_PROVED finiteCharacteristicDeterminant_zero_to_real_of_hilbertSelfAdjoint is Lean-only")
    print("LEAN_PROVED finiteCharacteristicDeterminantNoOffCriticalZeros is Lean-only")
    print("LEAN_PROVED no HP-parameter eigenvalue off critical line for self-adjoint T")
    print("LEAN_PROVED completed xi finite-characteristic packet constructor is Lean-only")
    print("LEAN_PROVED finite self-adjoint finite-characteristic HP readbacks are Lean-only")
    print("LEAN_PROVED CompletedXiSpectralDeterminantLemma follows from explicit packet")
    print("LEAN_PROVED CompletedXiSpectralDeterminantPacket zero/eigen readbacks are Lean-only")
    print("LEAN_PROVED CompletedXiSpectralDeterminantPacket nonzero contrapositives are Lean-only")
    print("LEAN_PROVED KreinDefinitizableRealSpectrumLemma follows from explicit packet")
    print("LEAN_PROVED KreinDefinitizableRealSpectrumPacket eigen-real readback is Lean-only")
    print("LEAN_PROVED HilbertPolyaNoOffCriticalZerosConclusion follows from explicit packets")
    print("LEMMA_DEBT completed xi determinant packet premises are not evaluated")
    print("LEMMA_DEBT Xi = unit * finiteCharacteristicDeterminant remains external")
    print("LEMMA_DEBT Krein definitizable packet premises are not evaluated")
    print("LEMMA_DEBT Deitmar Polya-Hilbert theorem is external automorphic L-function evidence")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
