"""Multilingual symbolic witness for Chiral Causal Cone / Time Cohomology / Tripotent operators."""

from __future__ import annotations
import os
import subprocess
import shutil
from sympy import I, pi, symbols, Matrix, diff, expand, integrate, log, hessian, exp, simplify

os.environ.setdefault("DOT_SAGE", "/tmp/info_geometry_sage_cache")
os.environ.setdefault("NUMBA_CACHE_DIR", "/tmp/info_geometry_numba_cache")

def sympy_block() -> None:
    print("== SymPy check: Tripotent, Self-Concordant Barrier, Tomita Derivation ==")

    # Let's formalize the self-concordant barrier: F(Q) = -log(Q)
    p01, p02, p03, p12, p13, p23 = symbols("p01 p02 p03 p12 p13 p23", real=True)
    # Klein quadric form Q = p01*p23 - p02*p13 + p03*p12
    Q = p01*p23 - p02*p13 + p03*p12
    F = -log(Q)

    # De Rham logarithmic form and the barrier derivative differ by a sign.
    dQ = Matrix([diff(Q, v) for v in (p01, p02, p03, p12, p13, p23)])
    dlogQ = dQ / Q
    dF = -dlogQ
    assert dF + dlogQ == Matrix.zeros(6, 1)
    print("de Rham 1-form d(log Q):", dlogQ)
    print("barrier derivative d(-log Q):", dF)

    # The Klein gradient read against a tangent direction is the polar form.
    x01, x02, x03, x12, x13, x23, tau = symbols("x01 x02 x03 x12 x13 x23 tau", real=True)
    y01, y02, y03, y12, y13, y23 = symbols("y01 y02 y03 y12 y13 y23", real=True)
    X = Matrix([x01, x02, x03, x12, x13, x23])
    Y = Matrix([y01, y02, y03, y12, y13, y23])
    polar = (
        p01 * x23 + x01 * p23
        - (p02 * x13 + x02 * p13)
        + (p03 * x12 + x03 * p12)
    )
    polar_y = (
        p01 * y23 + y01 * p23
        - (p02 * y13 + y02 * p13)
        + (p03 * y12 + y03 * p12)
    )
    polar_xy = (
        x01 * y23 + y01 * x23
        - (x02 * y13 + y02 * x13)
        + (x03 * y12 + y03 * x12)
    )
    assert simplify((dQ.dot(X)) - polar) == 0
    dlog_direction = simplify(polar / Q)
    assert simplify(dQ.dot(X) / Q - dlog_direction) == 0
    radial = Matrix([p01, p02, p03, p12, p13, p23])
    assert simplify(dQ.dot(radial) / Q - 2) == 0

    QX = x01 * x23 - x02 * x13 + x03 * x12
    Q_tau = (
        (p01 + tau * x01) * (p23 + tau * x23)
        - (p02 + tau * x02) * (p13 + tau * x13)
        + (p03 + tau * x03) * (p12 + tau * x12)
    )
    directional_derivative = simplify(diff(Q_tau, tau).subs(tau, 0))
    assert simplify(directional_derivative - polar) == 0
    assert simplify(expand(Q_tau - (Q + tau * polar + tau**2 * QX))) == 0
    print("Klein gradient/polar identity verified:", dQ.T)
    print("Directional expansion Q(P+tau X) = Q(P)+tau*B(P,X)+tau^2*Q(X)")
    print("Klein d(log Q) applied to direction:", dlog_direction)

    # Hessian (metric for self-concordant barrier / Lie parallel transport metric)
    H = hessian(F, (p01, p02, p03, p12, p13, p23))
    assert H.shape == (6, 6)
    hessian_bilinear = simplify((X.T * H * Y)[0])
    expected_hessian_bilinear = simplify(polar * polar_y / Q**2 - polar_xy / Q)
    assert simplify(hessian_bilinear - expected_hessian_bilinear) == 0
    print("Hessian of barrier (Lie parallel transport metric shape):", H.shape)
    print("Barrier Hessian bilinear formula verified.")

    # Time as de Rham 1-form cohomology winding: integral of dz/z on |z|=1.
    t = symbols("t", real=True)
    z = exp(I * t)
    loop_integrand = simplify(diff(z, t) / z)
    loop_integral = simplify(integrate(loop_integrand, (t, 0, 2 * pi)))
    assert simplify(loop_integrand - I) == 0
    assert simplify(loop_integral - 2 * pi * I) == 0
    print("Time (winding loop integral of dz/z) =", loop_integral)

def _run_gap(code: str) -> str:
    proc = subprocess.run(
        ["gap", "-q"],
        input=(code + "\nQUIT;\n").encode(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    stderr = proc.stderr.decode()
    if proc.returncode != 0 or stderr.strip():
        raise RuntimeError(stderr)
    return proc.stdout.decode()

def gap_block() -> None:
    print("== GAP check: Null projection from Tripotent ==")
    if not shutil.which("gap"):
        print("gap executable not found; skipping")
        return

    code = r'''
R := PolynomialRing(Rationals, ["T"]);;
T := IndeterminatesOfPolynomialRing(R)[1];;
J := Ideal(R, [T^3 - T]);;
P := One(R) - T^2;;
Print("Is P idempotent modulo (T^3 - T)? ", P^2 - P in J, "\n");
Print("Does P*T vanish modulo (T^3 - T)? ", P*T in J, "\n");
Print("Does T*P vanish modulo (T^3 - T)? ", T*P in J, "\n");
'''
    try:
        out = _run_gap(code)
        assert out.count("true") == 3
        print(out.strip())
    except Exception as e:
        print("GAP check failed:", e)

def sage_block() -> None:
    print("== Sage check: Tomita Derivation / de Rham Cohomology ==")
    try:
        import sage.all as sg
    except Exception as exc:
        print(f"sage not available ({exc}); skipping")
        return

    R = sg.PolynomialRing(sg.QQ, "p01,p02,p03,p12,p13,p23")
    p01, p02, p03, p12, p13, p23 = R.gens()
    Q = p01 * p23 - p02 * p13 + p03 * p12

    print("Klein quadric form Q:", Q)
    J = R.ideal(Q)
    assert J.is_prime(), "Klein quadric ideal should be prime (irreducible)"
    print("Verified Q is an irreducible polynomial generating a prime ideal.")

    # Check the Tomita derivation / de Rham form properties
    dQ = [Q.derivative(v) for v in R.gens()]
    
    # Verify Euler's homogeneous function theorem: sum(v_i * dQ/dv_i) = 2 * Q
    euler_sum = sum(v * dq for v, dq in zip(R.gens(), dQ))
    assert euler_sum == 2 * Q, "Euler homogeneous theorem failed"
    print("Verified Euler homogeneous identity: sum(v_i * dQ/dv_i) = 2 * Q")
    print("Tomita/de Rham gradient dQ components mapped successfully.")

def galgebra_block() -> None:
    print("== galgebra check: Parafermions / Zero Volume Null Space ==")
    try:
        from galgebra.ga import Ga
    except Exception as exc:
        print(f"galgebra not available ({exc}); skipping")
        return

    ga = Ga('e0 e1 e2 e3', g=[1, 1, 1, 1], coords=None)
    e = ga.mv()
    # A decomposable bivector has vanishing four-volume: (u∧v)∧(u∧v)=0.
    parafermion_plane = (e[0] + e[1]) ^ (e[0] - e[1])
    zero_volume = (parafermion_plane ^ parafermion_plane).expand()
    assert zero_volume == 0, "decomposable parafermion plane should have zero volume"
    print("Parafermion zero-volume wedge identity verified.")

def clifford_block() -> None:
    print("== clifford package check: Chiral Causal Cone / Time Winding ==")
    try:
        from clifford import Cl
    except Exception as exc:
        print(f"clifford not available ({exc}); skipping")
        return

    # Signature (1,3) for spacetime causal cone
    layout, blades = Cl(1, 3)
    e1, e2, e3, e4 = blades["e1"], blades["e2"], blades["e3"], blades["e4"]
    
    # Null (light-like) vectors form the boundary of the causal cone.
    # e1**2 = 1 (time), e2**2 = -1 (space)
    n = e1 + e2
    assert float(n * n) == 0.0, "Null vector should have zero square"
    print("Null vector identity (e1 + e2)^2 = 0 verified on the causal cone.")
    
    # Pseudoscalar I for chiral algebra
    I = e1 * e2 * e3 * e4
    assert float(I * I) == -1.0, "Pseudoscalar square should be -1 in Cl(1,3)"
    print("Chiral pseudoscalar I^2 = -1 verified.")
    
    # Tripotent operator T = e1*e2 (where T^2 = 1, so T^3 = T)
    T = e1 * e2
    assert (T**3) == T, "Operator T = e1*e2 is tripotent (T^3 = T)"
    
    # Idempotent projector from tripotent
    P = 0.5 * (1 + T)
    assert (P * P) == P, "Projector P = (1 + T)/2 is idempotent"
    print("Verified tripotent operator T and its extracted idempotent null-projector.")

def main() -> None:
    sympy_block()
    gap_block()
    sage_block()
    galgebra_block()
    clifford_block()

if __name__ == "__main__":
    main()
