#!/usr/bin/env python3
"""Finite audit for braided cocycle/Wilson/entropy triangle bookkeeping."""

edges = ["12", "21", "13", "31", "23", "32"]
rev = {"12": "21", "21": "12", "13": "31", "31": "13", "23": "32", "32": "23"}
swap12 = {"12": "21", "21": "12", "13": "23", "31": "32", "23": "13", "32": "31"}


def wilson(L):
    return L["12"] + L["23"] + L["31"]


def pullback_swap12(L):
    return {e: L[swap12[e]] for e in edges}


def main():
    assert all(rev[rev[e]] == e for e in edges)
    assert all(swap12[swap12[e]] == e for e in edges)

    entropy_cycle = {"12": 1, "23": 1, "31": 1, "21": -1, "32": -1, "13": -1}
    assert all(entropy_cycle[rev[e]] == -entropy_cycle[e] for e in edges)
    assert wilson(entropy_cycle) == 3
    assert wilson(entropy_cycle) != 0

    flat = {e: 0 for e in edges}
    assert wilson(flat) == 0

    defect = wilson(pullback_swap12(entropy_cycle)) - wilson(entropy_cycle)
    print("oriented edges:", edges)
    print("entropy cycle Wilson circulation:", wilson(entropy_cycle))
    print("flat/detailed-balance Wilson circulation:", wilson(flat))
    print("braid swap12 entropy defect for witness:", defect)
    print("nonzero Wilson circulation = broken detailed balance fingerprint")
    print("braided_cocycle_wilson_entropy.py: finite audit passed")


if __name__ == "__main__":
    main()
