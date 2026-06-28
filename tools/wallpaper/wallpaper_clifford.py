import sympy as sp
from clifford import Cl

layout, blades = Cl(2, 0, firstIdx=1)
e1 = blades['e1']
e2 = blades['e2']
B = e1 ^ e2


def main():
    rot180 = -1
    refl_x = sp.diag(1, -1)
    glide = sp.Matrix([[1, sp.Rational(1, 2)], [0, -1]])
    assert (B * B)[()] == -1
    assert rot180 * rot180 == 1
    assert refl_x * refl_x == sp.eye(2)
    assert glide * glide == sp.eye(2)
    print('bivector_square =', (B * B)[()])
    print('WALLPAPER_CLIFFORD_OK')


if __name__ == '__main__':
    main()
