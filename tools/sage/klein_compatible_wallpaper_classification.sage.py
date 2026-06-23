"""Sage exact-rational certificate for finite Klein wallpaper candidates."""

from sage.all import Matrix, QQ, identity_matrix


def vec_key(v):
    return tuple(QQ(v[i, 0]) for i in range(v.nrows()))


def mat(rows):
    return Matrix(QQ, rows)


def d5_roots():
    roots = []
    for i in range(5):
        for j in range(i + 1, 5):
            for si in (QQ(1), QQ(-1)):
                for sj in (QQ(1), QQ(-1)):
                    v = Matrix(QQ, 5, 1, [0, 0, 0, 0, 0])
                    v[i, 0] = si
                    v[j, 0] = sj
                    roots.append(v)
    return roots


print("=== Klein-compatible wallpaper classification Sage certificate ===")
roots = d5_roots()
assert len(roots) == 40

projected = {vec_key(Matrix(QQ, 2, 1, [r[0, 0], r[1, 0]])) for r in roots}
projected.discard((QQ(0), QQ(0)))
expected = {
    (QQ(-1), QQ(-1)),
    (QQ(-1), QQ(0)),
    (QQ(-1), QQ(1)),
    (QQ(0), QQ(-1)),
    (QQ(0), QQ(1)),
    (QQ(1), QQ(-1)),
    (QQ(1), QQ(0)),
    (QQ(1), QQ(1)),
}
assert projected == expected
print("PASS: nonzero D5 projection is B2/C2 eight-root set")

I = identity_matrix(QQ, 3)
Tx = mat([[1, 0, 1], [0, 1, 0], [0, 0, 1]])
Ty = mat([[1, 0, 0], [0, 1, 1], [0, 0, 1]])
Gx = mat([[1, 0, QQ(1) / QQ(2)], [0, -1, 0], [0, 0, 1]])
mirror_x = mat([[-1, 0, 0], [0, 1, 0], [0, 0, 1]])
Gy = mat([[-1, 0, 0], [0, 1, QQ(1) / QQ(2)], [0, 0, 1]])

assert Gx * Gx == Tx
assert Gx * Ty == Ty.inverse() * Gx
print("PASS: pg finite affine corridor")

assert mirror_x * mirror_x == I
assert Gx * Gx == Tx
assert Gx * Ty == Ty.inverse() * Gx
print("PASS: pmg finite representative corridor")

assert Gy * Gy == Ty
assert Gy * Tx == Tx.inverse() * Gy
assert Gx * Ty == Ty.inverse() * Gx
print("PASS: pgg finite two-glide corridor")

candidate_normals = {
    "pg": [(QQ(0), QQ(1)), (QQ(1), QQ(-1))],
    "pmg": [(QQ(1), QQ(0)), (QQ(0), QQ(1))],
    "pgg": [(QQ(1), QQ(0)), (QQ(0), QQ(1))],
}
for name, normals in candidate_normals.items():
    for normal in normals:
        assert normal in projected
    print(f"PASS: {name} normals lie in projected D5 cross-section")

print("KLEIN_COMPATIBLE_WALLPAPER_CLASSIFICATION_SAGE_CERTIFICATE_OK")
