import itertools
from fractions import Fraction

import sympy as sp
from sympy.functions.combinatorial.numbers import mobius


def squarefree_distinct_prime_count(n: int) -> tuple[bool, int]:
    factors = sp.factorint(n)
    squarefree = all(exp == 1 for exp in factors.values())
    return squarefree, len(factors)


def classify_mobius_value(mu_value: int) -> str:
    if mu_value == 1:
        return "boson"
    if mu_value == -1:
        return "fermion"
    return "ghost"


def fermion_partition(xs):
    out = Fraction(1, 1)
    for x in xs:
        out *= 1 + x
    return out


def signed_witten_partition(xs):
    out = Fraction(1, 1)
    for x in xs:
        out *= 1 - x
    return out


def second_order_signed_partition(xs):
    out = Fraction(1, 1)
    for x in xs:
        out *= 1 - x * x
    return out


def boson_partition(xs):
    out = Fraction(1, 1)
    for x in xs:
        if 1 - x == 0:
            raise ZeroDivisionError("boson partition requires 1 - x_p != 0")
        out *= Fraction(1, 1) / (1 - x)
    return out


def finite_witten_index(num_primes: int) -> int:
    total = 0
    for bits in itertools.product([0, 1], repeat=num_primes):
        total += (-1) ** sum(bits)
    return total


def verify_mobius_trifactor_readout(limit: int = 30) -> None:
    for n in range(1, limit + 1):
        mu_val = int(mobius(n))
        squarefree, distinct_primes = squarefree_distinct_prime_count(n)

        assert mu_val in (-1, 0, 1), f"mobius({n}) escaped trifactor: {mu_val}"

        if not squarefree:
            assert mu_val == 0, f"non-squarefree n={n} should have mobius 0"
            assert classify_mobius_value(mu_val) == "ghost"
        elif distinct_primes % 2 == 0:
            assert mu_val == 1, f"squarefree even-parity n={n} should have mobius 1"
            assert classify_mobius_value(mu_val) == "boson"
        else:
            assert mu_val == -1, f"squarefree odd-parity n={n} should have mobius -1"
            assert classify_mobius_value(mu_val) == "fermion"


def verify_finite_euler_factor_identities() -> None:
    test_sets = [
        [Fraction(1, 2)],
        [Fraction(1, 2), Fraction(1, 3)],
        [Fraction(1, 2), Fraction(1, 3), Fraction(1, 5)],
        [Fraction(-1, 2), Fraction(1, 4), Fraction(2, 5)],
    ]
    for xs in test_sets:
        ferm = fermion_partition(xs)
        signed = signed_witten_partition(xs)
        second = second_order_signed_partition(xs)
        boson = boson_partition(xs)

        assert ferm * signed == second, (
            f"fermion*signed != second-order for xs={xs}: {ferm}*{signed} vs {second}"
        )
        assert boson * second == ferm, (
            f"boson*second != fermion for xs={xs}: {boson}*{second} vs {ferm}"
        )


def verify_finite_witten_index_cancellation() -> None:
    for num_primes in range(1, 7):
        assert finite_witten_index(num_primes) == 0, (
            f"finite Witten index should vanish for nonempty register of size {num_primes}"
        )


def verify_supersymmetric_primon_gas() -> None:
    print("--- Supersymmetric Primon Gas: finite verified theorem surface ---")

    verify_mobius_trifactor_readout()
    print("1. Möbius/trifactor readout verified on n = 1..30")
    print("   - squarefree even parity -> boson (+1)")
    print("   - squarefree odd parity  -> fermion (-1)")
    print("   - repeated prime factor  -> ghost (0)")

    verify_finite_euler_factor_identities()
    print("2. Finite Euler-factor identities verified")
    print("   - fermionPartition * signedWittenPartition = secondOrderSignedPartition")
    print("   - bosonPartition * secondOrderSignedPartition = fermionPartition")

    verify_finite_witten_index_cancellation()
    print("3. Finite Boolean Witten-index cancellation verified on nonempty registers")

    print("4. Honest scope")
    print("   - verified: finite algebraic corridor only")
    print("   - not verified here: analytic continuation, zeta-zero spectral meaning, RH")


if __name__ == "__main__":
    verify_supersymmetric_primon_gas()
