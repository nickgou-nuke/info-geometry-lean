from sympy import Abs, Integer, log, simplify


def external_potential_energy(lam, potential):
    return sum(potential(x) for x in lam)


def log_interaction_energy(lam):
    total = Integer(0)
    for i in range(len(lam)):
        for j in range(i + 1, len(lam)):
            total += log(Abs(lam[j] - lam[i]))
    return total


def vandermonde_product_abs(lam):
    prod = Integer(1)
    for i in range(len(lam)):
        for j in range(i + 1, len(lam)):
            prod *= Abs(lam[j] - lam[i])
    return prod


def dyson_hamiltonian(lam, potential):
    return external_potential_energy(lam, potential) - 2 * log_interaction_energy(lam)


def verify_sample(lam, potential):
    prod = vandermonde_product_abs(lam)
    interaction = log_interaction_energy(lam)
    external = external_potential_energy(lam, potential)
    dyson = dyson_hamiltonian(lam, potential)

    assert prod != 0, f"sample has a collision: {lam}"
    assert simplify(log(prod) - interaction) == 0
    assert simplify(log(prod**2) - 2 * interaction) == 0
    assert simplify(dyson - (external - log(prod**2))) == 0

    return {
        "lambda": lam,
        "product": prod,
        "external": external,
        "interaction": interaction,
        "dyson": dyson,
    }


if __name__ == "__main__":
    potential = lambda x: x**2
    samples = [
        [Integer(1), Integer(3), Integer(6)],
        [Integer(-2), Integer(0), Integer(5)],
        [Integer(2), Integer(5), Integer(9), Integer(14)],
    ]

    print("Verifying finite Dyson/Vandermonde bridge samples...")
    for sample in samples:
        result = verify_sample(sample, potential)
        print(
            f"OK lambda={result['lambda']} product={result['product']} "
            f"dyson={result['dyson']}"
        )

    collision = [Integer(1), Integer(1), Integer(4)]
    collision_prod = vandermonde_product_abs(collision)
    assert collision_prod == 0
    print(f"Collision sample correctly collapses Vandermonde product to 0: {collision}")
    print("All finite SymPy assertions passed.")
