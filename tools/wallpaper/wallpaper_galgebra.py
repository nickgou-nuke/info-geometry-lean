import sympy as sp
from galgebra.ga import Ga

ga = Ga('e1 e2', g=[1, 1])
e1, e2 = ga.mv()
B = e1 ^ e2


def main():
    rot180 = (-1) * e1
    refl = e1
    assert (B * B).scalar() == -1
    assert refl * refl == 1
    print('bivector_square =', (B * B).scalar())
    print('reflection_generator =', refl)
    print('rot180_sample =', rot180)
    print('WALLPAPER_GALGEBRA_OK')


if __name__ == '__main__':
    main()
