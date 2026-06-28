import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DATA = json.loads((ROOT / 'wallpaper17_repdata.json').read_text())


def tokens_expr(token, z3, z6, I):
    table = {
        '0': SR(0),
        '1': SR(1),
        '-1': SR(-1),
        '2': SR(2),
        '-2': SR(-2),
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

from sage.all import I, SR, sqrt


def as_vec(row):
    z3 = -1/2 + I * sqrt(3) / 2
    z6 = 1/2 + I * sqrt(3) / 2
    return [tokens_expr(x, z3, z6, I) for x in row]


def verify_point_group(name, info):
    classes = info['class_sizes']
    chars = [as_vec(r) for r in info['characters']]
    order = info['order']
    assert sum(classes) == order
    for r in chars:
        assert sum(SR(c) * (v.conjugate() * v) for c, v in zip(classes, r)) == SR(order)
    for i, r in enumerate(chars):
        for j, s in enumerate(chars):
            inner = sum(SR(c) * a.conjugate() * b for c, a, b in zip(classes, r, s))
            if i == j:
                assert inner == SR(order)
            else:
                assert inner == 0


def main():
    for name, info in DATA['point_groups'].items():
        verify_point_group(name, info)
    case_meta = json.loads((ROOT / 'wallpaper17_cases.json').read_text())['cases']
    order_map = {c['name']: c['point_group_order'] for c in case_meta}
    for g, orbits in DATA['orbit_samples'].items():
        for o in orbits:
            assert o['stabilizer_order'] * o['orbit_size'] == order_map[g]
    print({'point_groups': len(DATA['point_groups']), 'orbit_tables': len(DATA['orbit_samples'])})
    print('WALLPAPER17_REP_SAGE_OK')


if __name__ == '__main__':
    main()
