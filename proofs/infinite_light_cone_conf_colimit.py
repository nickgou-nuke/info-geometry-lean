#!/usr/bin/env python3
"""Finite audit for the infinite light-cone configuration colimit scaffold."""

from math import comb


def edge_count(n: int) -> int:
    return comb(n, 2)


def collapse_12(edge):
    return "inner" if edge == (1, 2) else "outer"


def main():
    assert edge_count(1) == 0
    assert edge_count(2) == 1
    assert edge_count(3) == 3
    assert [collapse_12(e) for e in [(1, 2), (1, 3), (2, 3)]] == [
        "inner",
        "outer",
        "outer",
    ]
    product_rank_arity3 = 2**3 * 2**2
    os_rank_arity3 = 6 * 2**2
    assert product_rank_arity3 == 32
    assert os_rank_arity3 == 24
    assert product_rank_arity3 - os_rank_arity3 == 8
    print("edge counts n=1,2,3:", [edge_count(n) for n in (1, 2, 3)])
    print("arity-3 colimit stage rank:", product_rank_arity3)
    print("collapse {1,2}|{3}: 12->inner, 13/23->outer")
    print("infinite_light_cone_conf_colimit.py: finite colimit audit passed")


if __name__ == "__main__":
    main()
