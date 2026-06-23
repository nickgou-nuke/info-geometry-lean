# -*- coding: utf-8 -*-
"""
GAlgebra/Clifford Spinor Mapping for osp(1|2).

Constructs the Clifford algebra Cl(1,2) and the real sl2 representation
inside the even subalgebra Cl+(1,2). Projects onto the spinor left ideal
via P = (1 + e12)/2 and verifies the weights and actions.
"""

from sympy import symbols, simplify
from galgebra.ga import Ga

def main():
    print("==================================================================")
    print("GAlgebra: Spinor Mapping in Cl+(1,2) for osp(1|2)")
    print("==================================================================")

    # 1. Define Cl(1,2) with signature (1, -1, -1)
    ga = Ga('e1 e2 e3', g=[1, -1, -1])
    e1, e2, e3 = ga.mv_basis

    # Get bivector generators
    e12 = e1 * e2
    e23 = e2 * e3
    e13 = e1 * e3

    # 2. Define sl2 bivector generators (even subalgebra)
    H = e12
    Ep = (e13 - e23) / 2
    Em = (e13 + e23) / 2

    print("sl2 bivector generators:")
    print(f"  H  = {H}")
    print(f"  Ep = {Ep}")
    print(f"  Em = {Em}")

    # Verify sl2 commutation relations: [A, B] = A*B - B*A
    def comm(a, b):
        return simplify((a * b - b * a).obj)

    h_ep = comm(H, Ep)
    h_em = comm(H, Em)
    ep_em = comm(Ep, Em)

    print("\nVerifying sl2 bivector relations:")
    print(f"  [H, Ep]  = {h_ep}  (expected {simplify((2*Ep).obj)})")
    print(f"  [H, Em]  = {h_em}  (expected {simplify((-2*Em).obj)})")
    print(f"  [Ep, Em] = {ep_em}  (expected {simplify(H.obj)})")

    assert h_ep == simplify((2 * Ep).obj)
    assert h_em == simplify((-2 * Em).obj)
    assert ep_em == simplify(H.obj)
    print("  ✓ sl2 bivector relations verified successfully!")

    # 3. Spinor minimal left ideal of Cl+(1,2) via projector P = (1 + e12)/2
    P = (1 + e12) / 2
    print(f"\nProjector P = {P}")
    assert simplify((P * P - P).obj) == 0
    print("  ✓ Projector P is idempotent (P^2 = P)")

    # Define spinor basis of the left ideal Cl+(1,2)*P
    psi1 = P
    psi2 = e23 * P

    print("Spinor basis:")
    print(f"  psi1 = {psi1}")
    print(f"  psi2 = {psi2}")

    # 4. Verify spin-1/2 actions of sl2 bivectors on spinor basis
    # Action of bivector B on spinor psi is just left multiplication B*psi
    def act(b, psi):
        return simplify((b * psi).obj)

    print("\nVerifying spin-1/2 actions on spinor basis:")
    h_psi1 = act(H, psi1)
    h_psi2 = act(H, psi2)
    ep_psi1 = act(Ep, psi1)
    ep_psi2 = act(Ep, psi2)
    em_psi1 = act(Em, psi1)
    em_psi2 = act(Em, psi2)

    print(f"  H * psi1  = {h_psi1}  (expected {simplify(psi1.obj)})")
    print(f"  H * psi2  = {h_psi2}  (expected {simplify((-psi2).obj)})")
    print(f"  Ep * psi1 = {ep_psi1}  (expected 0)")
    print(f"  Ep * psi2 = {ep_psi2}  (expected {simplify(psi1.obj)})")
    print(f"  Em * psi1 = {em_psi1}  (expected {simplify(psi2.obj)})")
    print(f"  Em * psi2 = {em_psi2}  (expected 0)")

    assert simplify((H * psi1 - psi1).obj) == 0
    assert simplify((H * psi2 + psi2).obj) == 0
    assert ep_psi1 == 0
    assert simplify((Ep * psi2 - psi1).obj) == 0
    assert simplify((Em * psi1 - psi2).obj) == 0
    assert em_psi2 == 0
    print("  ✓ Spin-1/2 representation on the ideal verified successfully!")

    print("\nOVERALL: GAlgebra Cl(1,2) Spinor Mapping: PASSED")
    return 0

if __name__ == "__main__":
    import sys
    sys.exit(main())
