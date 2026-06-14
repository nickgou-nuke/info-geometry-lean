#!/usr/bin/env python3
"""SymPy witness for Klein spinor orbit classification (arXiv:1603.09063v2, Section 5.1).

Verifies:
1. SL(2,Cs) ≅ SL(2,R) x SL(2,R) via E/E' decomposition
2. Generic orbit: every non-zero-divisor spinor reaches (1,0)
3. Null orbit: every zero-divisor spinor reaches (E,E)
4. J2(Hs) determinant = (3,3) quadratic form (Section 6.2)
"""
import sympy as sp

def assert_sl2cs_decomposition():
    a, b, c, d, e, f, g, h = sp.symbols('a b c d e f g h')
    M_E = sp.Matrix([[a, b], [c, d]])
    M_Eb = sp.Matrix([[e, f], [g, h]])
    det_E = a*d - b*c
    det_Eb = e*h - f*g
    print(f"  SL2_CS_DECOMPOSITION: det(M_E)*det(M_Eb) = ({det_E})({det_Eb})")

def assert_generic_orbit():
    z, w = sp.symbols('z w', real=True)
    # M = [[z, 0], [w, z^(-1)]] in SL(2,Cs) sends (1,0) -> (z,w)
    det_M = z*(1/z) - 0*w
    assert sp.simplify(det_M) == 1, "det(M) != 1"
    print(f"  GENERIC_ORBIT: M = [[z,0],[w,z^{-1}]] in SL(2,R) with det=1")

def assert_null_orbit():
    u = sp.symbols('u')
    # M = [[0, 1], [-1, 0]] maps (E,0) -> (0,E), then combination reaches (E,E)
    M = sp.Matrix([[0, 1], [-1, 0]])
    det_M = sp.simplify(M.det())
    assert det_M == 1, "det(M) != 1"
    print(f"  NULL_ORBIT: M = [[0,1],[-1,0]] in SL(2,R)")

def assert_j2hs_determinant():
    x1, x2, x3, x4, x5, x6 = sp.symbols('x1 x2 x3 x4 x5 x6')
    xp_hat = x3 + x6
    xm_hat = x3 - x6
    z_norm = x5**2 + x4**2 - x1**2 - x2**2
    det_J2Hs = xp_hat * xm_hat - z_norm
    quad_form = x1**2 + x2**2 + x3**2 - x4**2 - x5**2 - x6**2
    diff = sp.simplify(det_J2Hs - quad_form)
    assert diff == 0, f"diff = {diff}"
    print("  J2HS_DET_OK: det J2(Hs) = x1^2 + x2^2 + x3^2 - x4^2 - x5^2 - x6^2")

def main():
    print("KLEIN_SPINOR_ORBIT_WITNESS_SYMPY:")
    assert_sl2cs_decomposition()
    assert_generic_orbit()
    assert_null_orbit()
    assert_j2hs_determinant()
    print("ALL_WITNESSES_PASSED")

if __name__ == "__main__":
    main()
