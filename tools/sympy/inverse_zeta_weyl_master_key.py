from itertools import combinations

from sympy import Matrix, Symbol, expand, simplify


def powerset(seq):
    seq = list(seq)
    out = []
    for r in range(len(seq) + 1):
        out.extend(combinations(seq, r))
    return out


def mobius_parity(cardinality):
    return -1 if cardinality % 2 else 1


def alternating_subset_sum(weights):
    items = list(weights.items())
    total = 0
    for subset in powerset(items):
        subset_keys = [k for k, _ in subset]
        subset_vals = [v for _, v in subset]
        sign = mobius_parity(len(subset))
        prod = 1
        for v in subset_vals:
          prod *= v
        total += sign * prod
    return simplify(total)


def main():
    w2, w3, w5 = Symbol("w2"), Symbol("w3"), Symbol("w5")
    weights = {2: w2, 3: w3, 5: w5}

    denominator = expand((1 - w2) * (1 - w3) * (1 - w5))
    alternating = alternating_subset_sum(weights)

    print("Inverse Zeta / Weyl / Witten finite master key")
    print("1. Alternating subset sum:")
    print(alternating)
    print("2. Finite Weyl denominator:")
    print(denominator)
    print("3. Product equality:")
    print(simplify(alternating - denominator) == 0)

    mobius_squarefree = mobius_parity(3)
    print("4. Möbius parity of 2*3*5:", mobius_squarefree)

    finite_bosonic_inverse = 1 / denominator
    print("5. Finite boson × Weyl denominator cancellation:")
    print(simplify(finite_bosonic_inverse * denominator - 1) == 0)

    # A tiny matrix witness for the parity supertrace as a signed diagonal readout.
    parity = Matrix.diag(1, -1, 1, -1)
    print("6. Signed trace of a toy parity operator:", parity.trace())


if __name__ == "__main__":
    main()
