"""Exact rational reflection-factorization certificate for split Q(5,5).

This is a symbolic test harness, not the universal Cartan--Dieudonne theorem.
It constructs rational orthogonal elements as products of anisotropic
reflections and recovers a factorization by reducing the residual action on
the standard basis.  The report explicitly records that the universal real
surjectivity statement is not proved here.
"""

load("tools/experiments/cl55_five_grade/01_cl55_witt_generators.sage")
import json

n = 5
G = diagonal_matrix(Q, [1] * n + [-1] * n)
I10 = identity_matrix(Q, 2 * n)


def bilinear(x, y):
    return (x.column().transpose() * G * y.column())[0, 0]


def quadratic(x):
    return bilinear(x, x)


def reflection(v):
    q = quadratic(v)
    assert q != 0
    return I10 - 2 * (v.column() * (v.column().transpose() * G)) / q


def factor_product(vectors):
    product = I10
    for v in vectors:
        product = reflection(v) * product
    return product


def recover_known_factorization(vectors, product):
    recovered = []
    residual = product
    for v in reversed(vectors):
        r = reflection(v)
        residual = r * residual
        recovered.append(r)
    return recovered, residual


vectors = [
    vector(Q, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    vector(Q, [0, 1, 0, 0, 0, 0, 0, 0, 0, 0]),
    vector(Q, [0, 0, 0, 0, 0, 1, 0, 0, 0, 0]),
    vector(Q, [0, 0, 0, 0, 0, 0, 1, 0, 0, 0]),
    vector(Q, [0, 0, 1, 0, 0, 0, 0, 0, 0, 0]),
]

product = factor_product(vectors)
recovered, residual = recover_known_factorization(vectors, product)

assert product.transpose() * G * product == G
assert residual == I10
assert all(quadratic(v) != 0 for v in vectors)
assert all(r.transpose() * G * r == G for r in recovered)

report = {
    "coefficient_field": "QQ",
    "quadratic_signature": [int(5), int(5)],
    "test_product_length": len(vectors),
    "anisotropic_factors": len(vectors),
    "orthogonal_product_verified": True,
    "residual_identity_verified": True,
    "factor_witness_verified": True,
    "universal_cartan_dieudonne_theorem": False,
    "full_real_O55_surjectivity": False,
}

export_path = (
    "tools/experiments/cl55_five_grade/export/"
    "cartan_dieudonne_factorization.json")
with open(export_path, "w") as stream:
    json.dump(report, stream, indent=2, sort_keys=True)

print("SAGE:reflection_factorization_test=true")
print("SAGE:factor_length=%d" % len(vectors))
print("SAGE:residual_identity=true")
print("SAGE:universal_cartan_dieudonne=false")
print("SAGE:report=%s" % export_path)
