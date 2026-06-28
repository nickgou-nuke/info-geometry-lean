#!/usr/bin/env python3
from clifford import Cl
from sympy import Matrix, Rational, simplify, symbols

layout, blades = Cl(2, 0, firstIdx=1)
e1 = blades['e1']
e2 = blades['e2']
B = e1 ^ e2


def quaternion_matrix(w, x, y, z):
    return Matrix([[w + x * 1j, y + z * 1j], [-y + z * 1j, w - x * 1j]])


def main():
    rotor = (1 + B) / (2 ** 0.5)
    rotor_rev = ~rotor
    v_rot = rotor * e1 * rotor_rev
    biv_sq = (B * B)[()]
    assert abs(float(biv_sq) + 1.0) < 1e-9

    M = Matrix([[2, 0], [0, Rational(1, 2)]])
    v_zero = Matrix([[1], [0]])
    v_inf = Matrix([[0], [1]])
    assert M * v_zero == 2 * v_zero
    assert M * v_inf == Rational(1, 2) * v_inf

    w, x, y, z = symbols('w x y z')
    H = Matrix([[w + x * 1j, y + z * 1j], [-y + z * 1j, w - x * 1j]])
    detH = simplify(H.det())

    print('bivector_square =', biv_sq)
    print('rotated_e1 =', v_rot)
    print('hyperbolic_eigenvalues = [2, 1/2]')
    print('hyperbolic_projective_directions = [0, infinity]')
    print('hurwitz_matrix_det =', detH)
    print('MOBIUS_CLIFFORD_OK')


if __name__ == '__main__':
    main()
