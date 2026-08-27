"""Discovery-only probe for the full peel on the seventh basis vector.

This script reports CAS data; it is not a Lean proof or a trust boundary.
"""

from collections import Counter

from verify_flag_stabilizer_full_peel_cas import subgroup
from verify_full_peel_residual_cas import mm, peel, s_gens


def word(bits):
    out = __import__("numpy").eye(8, dtype="int64")
    for bit, gen in zip(bits, s_gens):
        if bit:
            out = mm(out, gen)
    return out


def main():
    elements = subgroup([s_gens[0], s_gens[1], s_gens[2], s_gens[4]])
    e7 = __import__("numpy").zeros(8, dtype="int64")
    e7[7] = 1
    e6 = __import__("numpy").zeros(8, dtype="int64")
    e6[6] = 1
    images = Counter()
    images6 = Counter()
    residuals = Counter()
    for element in elements:
        bits, residual = peel(element)
        images[tuple((residual @ e7) % 2)] += 1
        images6[tuple((residual @ e6) % 2)] += 1
        residuals[tuple(residual.reshape(-1))] += 1
    print("FLAG_CLOSURE_CARD=", len(elements))
    print("FULL_PEEL_BASIS7_IMAGE_COUNT=", len(images))
    for image, count in sorted(images.items()):
        print("BASIS7_IMAGE", image, "COUNT", count)
    print("FULL_PEEL_BASIS6_IMAGE_COUNT=", len(images6))
    for image, count in sorted(images6.items()):
        print("BASIS6_IMAGE", image, "COUNT", count)
    print("FULL_PEEL_RESIDUAL_COUNT=", len(residuals))


if __name__ == "__main__":
    main()
