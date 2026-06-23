#!/usr/bin/env sage -python
"""Sage exact witness for the finite V4 / Q8 projective bridge."""

import os

os.environ.setdefault("TMPDIR", "/tmp")
os.environ.setdefault("SAGE_TMPDIR", "/tmp")

from sage.all import QQ, matrix, identity_matrix, ComplexField


def q8_elements():
    return ["1", "-1", "i", "-i", "j", "-j", "k", "-k"]


def q8_mul(a, b):
    # Table consistent with the standard quaternion relations.
    table = {
        ("1", x): x for x in q8_elements()
    }
    table.update({(x, "1"): x for x in q8_elements()})
    table.update({
        ("-1", "1"): "-1", ("-1", "-1"): "1",
    })
    core = {
        ("i", "i"): "-1",
        ("i", "j"): "k",
        ("i", "k"): "-j",
        ("j", "i"): "-k",
        ("j", "j"): "-1",
        ("j", "k"): "i",
        ("k", "i"): "j",
        ("k", "j"): "-i",
        ("k", "k"): "-1",
    }
    for (x, y), z in core.items():
        table[(x, y)] = z
        table[("-" + x, y)] = "-" + z if not z.startswith("-") else z[1:]
        table[(x, "-" + y)] = "-" + z if not z.startswith("-") else z[1:]
        table[("-" + x, "-" + y)] = z
    for x in ["i", "j", "k"]:
        table[("-1", x)] = "-" + x
        table[(x, "-1")] = "-" + x
        table[("-1", "-" + x)] = x
        table[("-" + x, "-1")] = x
    return table[(a, b)]


def regular_representation():
    Li = matrix(QQ, [
        [0, -1, 0, 0],
        [1,  0, 0, 0],
        [0,  0, 0, -1],
        [0,  0, 1, 0],
    ])
    Lj = matrix(QQ, [
        [0, 0, -1, 0],
        [0, 0,  0, 1],
        [1, 0,  0, 0],
        [0, -1, 0, 0],
    ])
    Lk = Li * Lj
    I4 = identity_matrix(QQ, 4)
    assert Li * Li == -I4
    assert Lj * Lj == -I4
    assert Lk * Lk == -I4
    assert Li * Lj == Lk
    assert Lj * Li == -Lk
    print("PASS: Sage exact rational quaternion matrices close")


def standard_complex_representation():
    C = ComplexField(53)
    I2 = identity_matrix(C, 2)
    qi = Matrix(C, [[C.gen(), 0], [0, -C.gen()]])
    qj = Matrix(C, [[0, 1], [-1, 0]])
    qk = qi * qj
    assert qi * qi == -I2
    assert qj * qj == -I2
    assert qk * qk == -I2
    assert qi * qj == qk
    assert qj * qi == -qk
    print("PASS: Sage standard 2x2 complex Q8 generators")


def quotient():
    quotient_map = {
        "1": "I", "-1": "I", "i": "W1", "-i": "W1",
        "j": "W2", "-j": "W2", "k": "W12", "-k": "W12",
    }
    v4 = {
        ("I", x): x for x in ["I", "W1", "W2", "W12"]
    }
    v4.update({(x, "I"): x for x in ["I", "W1", "W2", "W12"]})
    v4.update({
        ("W1", "W1"): "I",
        ("W1", "W2"): "W12",
        ("W1", "W12"): "W2",
        ("W2", "W1"): "W12",
        ("W2", "W2"): "I",
        ("W2", "W12"): "W1",
        ("W12", "W1"): "W2",
        ("W12", "W2"): "W1",
        ("W12", "W12"): "I",
    })
    for g in q8_elements():
        for h in q8_elements():
            assert quotient_map[q8_mul(g, h)] == v4[(quotient_map[g], quotient_map[h])]
    print("PASS: Q8 quotient collapses to V4")


print("=== V4 / Q8 Sage certificate ===")
regular_representation()
standard_complex_representation()
quotient()
print("Q8_V4_PROJECTIVE_BRIDGE_SAGE_CERTIFICATE_OK")
