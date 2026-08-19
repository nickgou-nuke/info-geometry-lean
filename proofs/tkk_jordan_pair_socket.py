#!/usr/bin/env python3
"""Finite audit for the abstract TKK five-grade bookkeeping deferred_interface."""

grades = {"m2": -2, "m1": -1, "z0": 0, "p1": 1, "p2": 2}
by_weight = {v: k for k, v in grades.items()}


def grade_add(a, b):
    return by_weight.get(grades[a] + grades[b])


def main():
    assert grade_add("z0", "p1") == "p1"
    assert grade_add("m1", "p1") == "z0"
    assert grade_add("m2", "p2") == "z0"
    assert grade_add("p2", "p1") is None
    assert grade_add("m2", "m1") is None

    print("tkk_jordan_pair_deferred_interface.py: five-grade bookkeeping passed")
    print("grade addition table ([g_i,g_j] subset g_{i+j}, outside window -> 0):")
    for a in grades:
        row = []
        for b in grades:
            row.append(grade_add(a, b) or "0")
        print(f"  {a}: {row}")
    print("Recommendation: abstract JordanPair/TKK interface first; instantiate Cuntz/Krein spacetime after bracket closure is proved.")
    print("RH/GUE/CUE/loop-braid links remain numerical/topological deferred_interfaces, not Lean theorems.")


if __name__ == "__main__":
    main()
