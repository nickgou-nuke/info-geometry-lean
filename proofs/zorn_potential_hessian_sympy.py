import sympy as sp

try:
    from galgebra.ga import Ga
except Exception:  # pragma: no cover
    Ga = None


def build_symbols():
    r, s = sp.symbols("r s", real=True)
    x1, x2, x3 = sp.symbols("x1 x2 x3", real=True)
    y1, y2, y3 = sp.symbols("y1 y2 y3", real=True)
    x = sp.Matrix([x1, x2, x3])
    y = sp.Matrix([y1, y2, y3])
    coords = sp.Matrix([r, s, x1, x2, x3, y1, y2, y3])
    return r, s, x, y, coords


def zorn_potential():
    r, s, x, y, coords = build_symbols()
    delta = sp.expand(r * s - (x.T * y)[0])
    phi = -sp.log(delta)
    grad_delta = sp.Matrix([s, r, -y[0], -y[1], -y[2], -x[0], -x[1], -x[2]])
    hess_delta = sp.zeros(8, 8)
    hess_delta[0, 1] = hess_delta[1, 0] = 1
    for i in range(3):
        hess_delta[2 + i, 5 + i] = -1
        hess_delta[5 + i, 2 + i] = -1
    hess_phi = sp.hessian(phi, list(coords))
    fisher_formula = sp.simplify((grad_delta * grad_delta.T) / delta**2 - hess_delta / delta)
    return {
        "delta": delta,
        "phi": phi,
        "coords": coords,
        "grad_delta": grad_delta,
        "grad_phi": sp.simplify(-grad_delta / delta),
        "hess_delta": hess_delta,
        "hess_phi": sp.simplify(hess_phi),
        "fisher_formula": fisher_formula,
        "closed_form_ok": sp.simplify(hess_phi - fisher_formula) == sp.zeros(8, 8),
    }


def galgebra_summary():
    if Ga is None:
        return "galgebra unavailable"
    u1, u2, u3 = sp.symbols("u1 u2 u3", real=True)
    ga = Ga("e1 e2 e3", g=[1, 1, 1])
    e1, e2, e3 = ga.mv()
    x_mv = u1 * e1 + u2 * e2 + u3 * e3
    return f"galgebra basis ok; sample Euclidean square = {(x_mv | x_mv).obj}"


def pretty_block_formula(delta, r, s, x, y):
    I3 = sp.eye(3)
    block = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.Matrix([[s**2, r * s - delta]]), -s * y.T, -s * x.T),
        sp.Matrix.hstack(sp.Matrix([[r * s - delta, r**2]]), -r * y.T, -r * x.T),
        sp.Matrix.hstack(-s * y, -r * y, y * y.T, y * x.T + delta * I3),
        sp.Matrix.hstack(-s * x, -r * x, x * y.T + delta * I3, x * x.T),
    )
    return sp.simplify(block / delta**2)


def main():
    data = zorn_potential()
    delta = data["delta"]
    phi = data["phi"]
    coords = data["coords"]
    grad_phi = data["grad_phi"]
    hess_phi = data["hess_phi"]
    closed_form_ok = data["closed_form_ok"]

    r, s, x, y, _ = build_symbols()
    block_formula = pretty_block_formula(delta, r, s, x, y)
    block_ok = sp.simplify(hess_phi - block_formula) == sp.zeros(8, 8)

    print("Zorn determinant Δ =")
    sp.pprint(delta)
    print("\nPotential Φ = -log(Δ) =")
    sp.pprint(phi)
    print("\nGradient ∇Φ =")
    sp.pprint(grad_phi)
    print("\nHessian H = ∇²Φ =")
    sp.pprint(hess_phi)
    print("\nClosed form identity H = (∇Δ∇Δᵀ)/Δ² - (∇²Δ)/Δ :", closed_form_ok)
    print("Block-matrix closed form verified:", block_ok)
    print("\nConstant Hessian of Δ =")
    sp.pprint(data["hess_delta"])
    print("\nGalgebra check:", galgebra_summary())


if __name__ == "__main__":
    main()
