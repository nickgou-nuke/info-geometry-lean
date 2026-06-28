import json
from pathlib import Path
from sage.all import Matrix, QQ

ROOT = Path(__file__).resolve().parent
CASES = json.loads((ROOT / 'wallpaper17_cases.json').read_text())['cases']
POINT_GROUP_ORDERS = {'C1': 1, 'C2': 2, 'D1': 2, 'V4': 4, 'C4': 4, 'D4': 8, 'C3': 3, 'D3': 6, 'C6': 6, 'D6': 12}


def q(x):
    s = str(x)
    if '/' in s:
        a, b = s.split('/')
        return QQ(int(a)) / QQ(int(b))
    return QQ(s)


def to_matrix(rows):
    return Matrix(QQ, [[q(x) for x in row] for row in rows])


def symmetry_keys(mc):
    return [k for k in mc if (k == 'symmetry' or (k.startswith('symmetry') and k[8:].isdigit())) and mc[k] is not None]


def verify_metadata(case):
    assert POINT_GROUP_ORDERS[case['point_group']] == case['point_group_order']
    assert case['one_dimensional'] + 4 * case['two_dimensional'] == case['point_group_order']
    assert case['irrep_total'] == case['one_dimensional'] + case['two_dimensional']


def verify_matrix_case(case):
    mc = case['matrix_case']
    tx = to_matrix(mc['translation_x'])
    ty = to_matrix(mc['translation_y'])
    tc = to_matrix(mc['translation_c']) if 'translation_c' in mc else None

    for key in symmetry_keys(mc):
        s = to_matrix(mc[key])
        idx = key[8:]
        target = mc.get('symmetry_square' + idx)
        if target == 'identity':
            assert s * s == Matrix.identity(QQ, 3)
        elif target == 'tx':
            assert s * s == tx
        elif target == 'ty':
            assert s * s == ty
        elif target == 'tc' and tc is not None:
            assert s * s == tc
        elif target == 'minus_identity_linear':
            assert s * s == Matrix(QQ, [[-1, 0, 0], [0, -1, 0], [0, 0, 1]])
        elif target == 'cube_identity':
            assert s**3 == Matrix.identity(QQ, 3)
        elif target == 'six_identity':
            assert s**6 == Matrix.identity(QQ, 3)
        elif target is None:
            pass
        else:
            raise ValueError((case['name'], key, target))

        conj = mc.get('conjugation_target' + idx)
        if conj == 'tx_inv':
            assert s * tx * s.inverse() == tx.inverse()
        elif conj == 'ty_inv':
            assert s * ty * s.inverse() == ty.inverse()
        elif conj == 'swap':
            assert s * tx * s.inverse() == ty
        elif conj == 'hex_mix':
            assert s * tx * s.inverse() == ty
        elif conj == 'mixed' or conj is None:
            pass
        else:
            raise ValueError((case['name'], key, conj))


def main():
    matrix_names = []
    for case in CASES:
        verify_metadata(case)
        if 'matrix_case' in case:
            verify_matrix_case(case)
            matrix_names.append(case['name'])
    print({'total_groups': len(CASES), 'matrix_verified': matrix_names})
    print('WALLPAPER17_SAGE_OK')


if __name__ == '__main__':
    main()
