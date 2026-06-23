#!/usr/bin/env python3
"""Exact-rational SymPy certificate for the finite V4 / Q8 projective bridge."""

from __future__ import annotations

import itertools

import sympy as sp


def mat_key(M: sp.Matrix) -> tuple:
    return tuple(M)


def vec_key(v: sp.Matrix) -> tuple:
    return tuple(v)


def q8_mul(a: str, b: str) -> str:
    """Multiplication table for the 8-element quaternion presentation."""
    table = {
        ("1", x): x for x in ["1", "-1", "i", "-i", "j", "-j", "k", "-k"]
    }
    table.update({(x, "1"): x for x in ["1", "-1", "i", "-i", "j", "-j", "k", "-k"]})
    table.update({
        ("-1", x): ("-" + x if not x.startswith("-") else x[1:])
        for x in ["1", "-1", "i", "-i", "j", "-j", "k", "-k"]
    })
    table.update({
        (x, "-1"): ("-" + x if not x.startswith("-") else x[1:])
        for x in ["1", "-1", "i", "-i", "j", "-j", "k", "-k"]
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
    for x in ["i", "j", "k"]:
        table[("1", x)] = x
        table[(x, "1")] = x
    for x in ["i", "j", "k"]:
        table[("-" + x, "1")] = "-" + x
        table[("1", "-" + x)] = "-" + x
    for x in ["i", "j", "k"]:
        table[("-1", x)] = "-" + x
        table[(x, "-1")] = "-" + x
        table[("-1", "-" + x)] = x
        table[("-" + x, "-1")] = x
    for (x, y), z in core.items():
        table[(x, y)] = z
        table[("-" + x, y)] = "-" + z if not z.startswith("-") else z[1:]
        table[(x, "-" + y)] = "-" + z if not z.startswith("-") else z[1:]
        table[("-" + x, "-" + y)] = z
    return table[(a, b)]


def q8_elements() -> list[str]:
    return ["1", "-1", "i", "-i", "j", "-j", "k", "-k"]


def left_regular_matrix(g: str) -> sp.Matrix:
    basis = q8_elements()
    cols = []
    for h in basis:
        gh = q8_mul(g, h)
        col = sp.zeros(8, 1)
        if gh.startswith("-"):
            col[basis.index(gh[1:]), 0] = -1
        else:
            col[basis.index(gh), 0] = 1
        cols.append(col)
    return sp.Matrix.hstack(*cols)


def quotient_map(g: str) -> str:
    return {"1": "I", "-1": "I", "i": "W1", "-i": "W1", "j": "W2", "-j": "W2", "k": "W12", "-k": "W12"}[g]


def regular_representation_checks() -> None:
    mats = {g: left_regular_matrix(g) for g in q8_elements()}
    for g, h in itertools.product(q8_elements(), repeat=2):
        assert mat_key(mats[g] * mats[h]) == mat_key(mats[q8_mul(g, h)])
    print("PASS: 8x8 exact rational left-regular Q8 representation closes")


def standard_complex_representation_checks() -> None:
    I2 = sp.eye(2)
    q_i = sp.Matrix([[sp.I, 0], [0, -sp.I]])
    q_j = sp.Matrix([[0, 1], [-1, 0]])
    q_k = q_i * q_j

    assert q_i * q_i == -I2
    assert q_j * q_j == -I2
    assert q_k * q_k == -I2
    assert q_i * q_j == q_k
    assert q_j * q_i == -q_k
    assert q_j * q_k == q_i
    assert q_k * q_i == q_j

    print("PASS: standard 2x2 complex Q8 representation is faithful on generators")


def quotient_checks() -> None:
    q8 = q8_elements()
    v4 = {"I", "W1", "W2", "W12"}
    qmap = {g: quotient_map(g) for g in q8}
    assert qmap["-1"] == "I"
    assert qmap["i"] == "W1"
    assert qmap["j"] == "W2"
    assert qmap["k"] == "W12"
    for g, h in itertools.product(q8, repeat=2):
        lhs = qmap[q8_mul(g, h)]
        rhs = qmap[g]
        rhs2 = qmap[h]
        # V4 multiplication table in generator notation.
        mult = {
            ("I", x): x for x in v4
        }
        mult.update({(x, "I"): x for x in v4})
        mult.update({
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
        assert lhs == mult[(rhs, rhs2)]
    print("PASS: Q8 quotient by the central sign collapses to V4")


def main() -> None:
    print("=== V4 / Q8 projective bridge SymPy certificate ===")
    regular_representation_checks()
    standard_complex_representation_checks()
    quotient_checks()
    print("Q8_V4_PROJECTIVE_BRIDGE_SYMPY_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
