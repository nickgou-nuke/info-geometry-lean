"""Finite SymPy audit for the Cantor/KMS holographic split.

This mirrors the Lean theorem `cylinderKMSWeight_children_sum` in
`InfoGeometry.Canonical.CantorKMSCylinderState`.

Scope:
* dyadic cylinder weights only;
* no C*-completion;
* no GNS representation;
* no global holography theorem.
"""

from sympy import Rational, simplify


def cylinder_weight(length: int):
    return Rational(1, 2) ** length


def main() -> None:
    parent = cylinder_weight(4)
    left = cylinder_weight(5)
    right = cylinder_weight(5)
    split_sum = simplify(left + right - parent)

    depth_one_left = cylinder_weight(1)
    depth_one_right = cylinder_weight(1)
    partition_sum = simplify(depth_one_left + depth_one_right)

    print("Cantor/KMS holographic split audit")
    print("----------------------------------")
    print(f"parent cylinder weight (depth 4): {parent}")
    print(f"child cylinder weight  (depth 5): {left}")
    print(f"child cylinder weight  (depth 5): {right}")
    print(f"children sum minus parent: {split_sum}")
    print(f"depth-one partition sum: {partition_sum}")

    assert split_sum == 0
    assert partition_sum == 1
    print("[OK] finite dyadic split returns the parent cylinder weight.")


if __name__ == "__main__":
    main()
