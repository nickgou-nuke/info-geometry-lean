from __future__ import annotations

import itertools
import json
from fractions import Fraction


def weight(word: tuple[bool, ...]) -> Fraction:
    return Fraction(1, 2) ** len(word)


def main() -> None:
    max_depth = 5
    branch_checks = []
    total_mass_checks = []
    for n in range(max_depth + 1):
        words = list(itertools.product([False, True], repeat=n))
        total = sum(weight(w) for w in words)
        total_mass_checks.append({"depth": n, "total_mass": str(total)})
        assert total == Fraction(1, 1), (n, total)

        for w in words:
            left = weight((False,) + w)
            right = weight((True,) + w)
            parent = weight(w)
            branch_checks.append(
                {
                    "word": "".join("1" if b else "0" for b in w),
                    "parent": str(parent),
                    "children_sum": str(left + right),
                }
            )
            assert left + right == parent, (w, left, right, parent)

    print(json.dumps({
        "certificate": "cantor_cylinder_prior_consistency",
        "max_depth": max_depth,
        "branch_checks": len(branch_checks),
        "total_mass_checks": total_mass_checks,
        "uniform_prior": "2^(-|w|)",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
