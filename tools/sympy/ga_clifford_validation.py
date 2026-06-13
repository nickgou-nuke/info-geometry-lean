import sympy as sp
from galgebra.ga import Ga
from clifford import Cl

def verify_galgebra():
    print("=== SGAE / GALGEBRA / CLIFFORD VALIDATION ===")

    # 1. galgebra Validation (Symbolic GA)
    coords = sp.symbols('x y z')
    ga3d = Ga('e', g=[1, 1, 1], coords=coords)
    e1, e2, e3 = ga3d.mv()

    # Bivector squaring to -1
    bivector_12 = e1 * e2
    assert (bivector_12 * bivector_12).obj == -1, "galgebra bivector square failed"
    print("[SUCCESS] galgebra: Symbolic Geometric Algebra verified (e12^2 = -1).")

    # 2. clifford Validation (Numerical GA)
    layout, blades = Cl(3)
    e1_c, e2_c, e3_c = blades['e1'], blades['e2'], blades['e3']

    # Bivector squaring to -1
    bivector_12_c = e1_c * e2_c
    assert bivector_12_c * bivector_12_c == -1, "clifford bivector square failed"
    print("[SUCCESS] clifford: Numerical Geometric Algebra verified (e12^2 = -1).")

    print("\n[COMPLETE] Both SGAE / Geometric Algebra engines tested successfully.")

if __name__ == '__main__':
    verify_galgebra()
