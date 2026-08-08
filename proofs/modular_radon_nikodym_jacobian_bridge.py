#!/usr/bin/env python3
"""SymPy audit for modular RN / negative log Jacobian bridge.

This is an audit witness only.  Lean remains the proof kernel.
"""

import sympy as sp


def main() -> None:
    t, s = sp.symbols("t s", real=True)
    a, b = sp.symbols("a b", real=True)  # infinitesimal dilation rates
    x, y = sp.symbols("x y", real=True)
    r1, r2 = sp.symbols("r1 r2", positive=True)

    # Two linear vacuum-form flows on R^2:
    # F_t = exp(a t) Id, G_s = exp(b s) Id.
    JF = sp.exp(2 * a * t)
    JG = sp.exp(2 * b * s)
    Jcomp = sp.simplify(JF * JG)

    log_add = sp.simplify(sp.log(Jcomp) - (sp.log(JF) + sp.log(JG)))
    neg_log_comp = sp.simplify(-sp.log(Jcomp) - (-sp.log(JF) - sp.log(JG)))

    # Infinitesimal negative log Jacobian = - divergence for X=a(x∂x+y∂y).
    X = sp.Matrix([a * x, a * y])
    div_X = sp.diff(X[0], x) + sp.diff(X[1], y)
    infinitesimal_neg_logJ = sp.diff(-sp.log(JF), t).subs(t, 0)
    assert sp.simplify(infinitesimal_neg_logJ + div_X) == 0

    # Forbidden-cone dlog clock audit.  For Q=x^2+y^2, the radial vector field
    # clocks log Q by L_X(log Q)=dlog(Q)(X)=2a, matching div X and hence
    # -d/dt log J = -dlog(Q)(X) in this 2D toy model.
    Q = x**2 + y**2
    grad_logQ = sp.Matrix([sp.diff(sp.log(Q), x), sp.diff(sp.log(Q), y)])
    dlogQ_on_X = sp.simplify((grad_logQ.dot(X)))
    assert sp.simplify(dlogQ_on_X - div_X) == 0
    assert sp.simplify(infinitesimal_neg_logJ + dlogQ_on_X) == 0

    # RN potentials: negative logs add under product of densities.
    rn_add = sp.simplify(-sp.log(r1 * r2) - (-sp.log(r1) - sp.log(r2)))

    # Finite modular automorphism in matrices: sigma_t(A)=exp(tK) A exp(-tK).
    k1, k2 = sp.symbols("k1 k2")
    A00, A01, A10, A11 = sp.symbols("A00 A01 A10 A11")
    eps = sp.symbols("eps")
    K = sp.diag(k1, k2)
    A = sp.Matrix([[A00, A01], [A10, A11]])
    expK = sp.diag(sp.exp(eps * k1), sp.exp(eps * k2))
    sigma = expK * A * expK.inv()
    delta = sigma.diff(eps).subs(eps, 0)
    commutator = K * A - A * K
    assert sp.simplify(delta - commutator) == sp.zeros(2)

    # Chemical potential exact edge one-form on triangle.
    mu1, mu2, mu3 = sp.symbols("mu_1 mu_2 mu_3", real=True)
    alpha12 = mu2 - mu1
    alpha23 = mu3 - mu2
    alpha31 = mu1 - mu3
    assert sp.simplify(alpha12 + alpha23 + alpha31) == 0

    # Forbidden-cone local normal coordinate u=Q.  The logarithmic generator
    # dlog(u) has unit residue, and one winding shifts log(u) by 2*pi*i.
    u = sp.symbols("u", nonzero=True)
    n = sp.symbols("n", integer=True)
    dlog_u = sp.diff(sp.log(u), u)
    assert sp.simplify(dlog_u - 1 / u) == 0
    sheeted_log_u = sp.log(u) + 2 * sp.pi * sp.I * n
    assert sp.simplify(sp.exp(sheeted_log_u) - u) == 0

    # Parabolic modular clock: P(t)P(s)=P(t+s).
    N = sp.Matrix([[0, 1], [0, 0]])
    I2 = sp.eye(2)
    pt, ps = sp.symbols("pt ps", real=True)
    P_t = I2 + pt * N
    P_s = I2 + ps * N
    P_ts = I2 + (pt + ps) * N
    assert (P_t * P_s - P_ts).applyfunc(sp.simplify) == sp.zeros(2)

    assert log_add == 0
    assert neg_log_comp == 0
    assert rn_add == 0

    print("JF =", JF)
    print("JG =", JG)
    print("log(JF*JG)-logJF-logJG =", log_add)
    print("-log(JF*JG)-(-logJF-logJG) =", neg_log_comp)
    print("div X =", div_X)
    print("dlog(Q)(X) =", dlogQ_on_X)
    print("d/dt|-0 (-log JF) =", infinitesimal_neg_logJ)
    print("RN -log product additivity =", rn_add)
    print("modular derivation delta(A) =")
    sp.pprint(delta)
    print("[K,A] =")
    sp.pprint(commutator)
    print("triangle exact affinity =", sp.simplify(alpha12 + alpha23 + alpha31))
    print("forbidden cone dlog normal derivative =", dlog_u)
    print("sheeted exp(log u + 2*pi*i*n)-u =", sp.simplify(sp.exp(sheeted_log_u) - u))
    print("parabolic clock P(pt)P(ps)-P(pt+ps) =")
    sp.pprint((P_t * P_s - P_ts).applyfunc(sp.simplify))
    print("modular_radon_nikodym_jacobian_bridge.py: finite audit passed")


if __name__ == "__main__":
    main()
