#!/usr/bin/env sage -python
"""
Exact-rational Sage certificate for the KL symmetric/antisymmetric decomposition.
"""

from sage.all import QQ, log


def kl_binary(p, q):
    return p * log(p / q) + (1 - p) * log((1 - p) / (1 - q))


def main() -> None:
    print("=== KL DIVERGENCE DECOMPOSITION SAGE CERTIFICATE ===")
    samples = [
        (QQ(1) / QQ(5), QQ(2) / QQ(5)),
        (QQ(1) / QQ(3), QQ(3) / QQ(5)),
        (QQ(2) / QQ(7), QQ(5) / QQ(8)),
    ]
    for p, q in samples:
        dpq = kl_binary(p, q)
        dqp = kl_binary(q, p)
        dsym = (dpq + dqp) / 2
        dasym = (dpq - dqp) / 2
        print(f"sample p={p}, q={q}")
        print("  D(p||q)   =", dpq.n())
        print("  D(q||p)   =", dqp.n())
        print("  D_sym     =", dsym.n())
        print("  D_antisym =", dasym.n())
        assert (dpq - (dsym + dasym)).simplify_full() == 0
        assert (dqp - (dsym - dasym)).simplify_full() == 0
        assert (((dqp + dpq) / 2) - dsym).simplify_full() == 0
        assert (((dqp - dpq) / 2) + dasym).simplify_full() == 0
    print("KL_DIVERGENCE_DECOMPOSITION_SAGE_OK")


if __name__ == "__main__":
    main()
