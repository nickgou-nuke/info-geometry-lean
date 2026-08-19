#!/usr/bin/env python3
"""Index arithmetic witness for Dupont's hypersurface Orlik-Solomon model.

Dupont's model has summands

  M_q^n(X,L) = direct sum_S H^{2n-q}(S)(n-q) tensor A_S(L)

with product

  M_q^n tensor M_q'^n' -> M_{q+q'}^{n+n'}

and differential

  d : M_q^n -> M_q^{n+1}

whose stratum component uses a Gysin map

  H^{2n-q}(S)(n-q) -> H^{2n-q+2}(S')(n-q+1).

This script checks the integer degree identities that our Lean deferred_interface uses.
"""

from __future__ import annotations


def cohom_degree(n: int, q: int) -> int:
    return 2 * n - q


def tate_twist(n: int, q: int) -> int:
    return n - q


def codim(n: int, q: int) -> int:
    return q - n


def product_sign_exponent(n: int, q: int, q_prime: int) -> int:
    return (q - n) * q_prime


def main() -> None:
    for n in range(0, 8):
        for n_prime in range(0, 8):
            for q in range(n, n + 6):
                for q_prime in range(n_prime, n_prime + 6):
                    assert cohom_degree(n, q) + cohom_degree(n_prime, q_prime) == cohom_degree(
                        n + n_prime, q + q_prime
                    )
                    assert tate_twist(n, q) + tate_twist(n_prime, q_prime) == tate_twist(
                        n + n_prime, q + q_prime
                    )
                    assert codim(n, q) + codim(n_prime, q_prime) == codim(
                        n + n_prime, q + q_prime
                    )

                    assert cohom_degree(n + 1, q) == cohom_degree(n, q) + 2
                    assert tate_twist(n + 1, q) == tate_twist(n, q) + 1
                    assert codim(n + 1, q) == codim(n, q) - 1
                    assert product_sign_exponent(n, q, q_prime) == codim(n, q) * q_prime

    print("dupont_hypersurface_os_model.py: index arithmetic passed")
    print("product: (2n-q)+(2n'-q') = 2(n+n')-(q+q')")
    print("differential/Gysin: 2(n+1)-q = 2n-q+2")
    print("codim shift: q-(n+1) = q-n-1")


if __name__ == "__main__":
    main()
