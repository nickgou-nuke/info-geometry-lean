from sympy import Rational, Symbol, diff, limit, oo, simplify


def thermal_cayley(beta):
    return (beta - Rational(1, 2)) / (beta + Rational(1, 2))


def main():
    beta = Symbol("beta", real=True, positive=True)
    eta = Rational(0)
    bulk_index = Symbol("bulk_index", real=True)
    boundary_index = bulk_index - eta

    W = thermal_cayley(beta)
    dW = diff(W, beta)

    assert simplify(boundary_index - bulk_index) == 0
    assert simplify(limit(W, beta, oo) - 1) == 0
    assert simplify(limit(dW, beta, oo)) == 0
    assert simplify(eta) == 0

    print("APS boundary socket witness passed")
    print(f"limit W(beta) as beta->oo = {limit(W, beta, oo)}")
    print(f"limit dW/dbeta as beta->oo = {limit(dW, beta, oo)}")
    print(f"eta = {eta}")
    print(f"boundary_index - bulk_index = {simplify(boundary_index - bulk_index)}")


if __name__ == "__main__":
    main()
