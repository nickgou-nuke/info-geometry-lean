import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DATA = json.loads((ROOT / 'wallpaper17_repdata.json').read_text())


def tokens_expr(token, z3, z6, I):
    table = {
        '0': 0,
        '1': 1,
        '-1': -1,
        '2': 2,
        '-2': -2,
        'i': I,
        '-i': -I,
        'w3': z3,
        'w3^2': z3**2,
        'z6': z6,
        'z6^2': z6**2,
        'z6^4': z6**4,
        'z6^5': z6**5,
    }
    return table[token]

import sympy as sp


def as_vec(row):
    z3 = -sp.Rational(1, 2) + sp.sqrt(3) * sp.I / 2
    z6 = sp.Rational(1, 2) + sp.sqrt(3) * sp.I / 2
    return [sp.simplify(tokens_expr(x, z3, z6, sp.I)) for x in row]


def verify_point_group(name, info):
    classes = info['class_sizes']
    chars = [as_vec(r) for r in info['characters']]
    order = info['order']
    assert sum(classes) == order
    for r in chars:
        assert sum(c * abs(v)**2 for c, v in zip(classes, r)) == order
    for i, r in enumerate(chars):
        for j, s in enumerate(chars):
            inner = sp.simplify(sum(c * sp.conjugate(a) * b for c, a, b in zip(classes, r, s)))
            if i == j:
                assert sp.simplify(inner - order) == 0
            else:
                assert sp.simplify(inner) == 0


def main():
    for name, info in DATA['point_groups'].items():
        verify_point_group(name, info)
    case_meta = json.loads((ROOT / 'wallpaper17_cases.json').read_text())['cases']
    order_map = {c['name']: c['point_group_order'] for c in case_meta}
    for g, orbits in DATA['orbit_samples'].items():
        for o in orbits:
            assert o['stabilizer_order'] * o['orbit_size'] == order_map[g]
    print({'point_groups': len(DATA['point_groups']), 'orbit_tables': len(DATA['orbit_samples'])})
    print('WALLPAPER17_REP_SYMPY_OK')


if __name__ == '__main__':
    main()
