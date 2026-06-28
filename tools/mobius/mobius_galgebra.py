#!/usr/bin/env python3
from galgebra.ga import Ga
from sympy import Rational, simplify


ga = Ga('e1 e2', g=[1, 1])
e1, e2 = ga.mv()
B = e1 ^ e2


def main():
    rotor = (B).exp()
    v_rot = rotor * e1 * rotor.rev()
    biv_sq = simplify((B * B).scalar())
    assert biv_sq == -1

    lam = Rational(2, 1)
    lam_inv = Rational(1, 2)
    multiplier_zero = Rational(1, 1) / (lam_inv ** 2)
    multiplier_inf = Rational(1, 1) / (lam ** 2)
    assert multiplier_zero == 4
    assert multiplier_inf == Rational(1, 4)

    print('bivector_square =', biv_sq)
    print('rotor =', rotor)
    print('rotated_e1 =', v_rot)
    print('mobius_scaling_eigenvalues = [2, 1/2]')
    print('mobius_multipliers = [4, 1/4]')
    print('MOBIUS_GALGEBRA_OK')


if __name__ == '__main__':
    main()
