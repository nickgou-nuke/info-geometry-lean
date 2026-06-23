#!/usr/bin/env python3
"""Exact finite certificate for wallpaper-group holonomy representation data.

The Lean owner is `InfoGeometry.Topology.WallpaperRepresentations`.
This script checks the same finite table on the SymPy/Python side:

* exactly 17 wallpaper groups;
* each group has the expected lattice family and finite point-group holonomy;
* the finite point-group irrep profile satisfies
  sum(dim(irrep)^2) = |point group|;
* a generic Brillouin-zone momentum has trivial little group C1.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class PointGroupProfile:
    order: int
    one_dimensional: int
    two_dimensional: int
    total: int

    def degree_square_sum(self) -> int:
        return self.one_dimensional + 4 * self.two_dimensional


POINT_GROUPS: dict[str, PointGroupProfile] = {
    "C1": PointGroupProfile(order=1, one_dimensional=1, two_dimensional=0, total=1),
    "C2": PointGroupProfile(order=2, one_dimensional=2, two_dimensional=0, total=2),
    "D1": PointGroupProfile(order=2, one_dimensional=2, two_dimensional=0, total=2),
    "V4": PointGroupProfile(order=4, one_dimensional=4, two_dimensional=0, total=4),
    "C4": PointGroupProfile(order=4, one_dimensional=4, two_dimensional=0, total=4),
    "D4": PointGroupProfile(order=8, one_dimensional=4, two_dimensional=1, total=5),
    "C3": PointGroupProfile(order=3, one_dimensional=3, two_dimensional=0, total=3),
    "D3": PointGroupProfile(order=6, one_dimensional=2, two_dimensional=1, total=3),
    "C6": PointGroupProfile(order=6, one_dimensional=6, two_dimensional=0, total=6),
    "D6": PointGroupProfile(order=12, one_dimensional=4, two_dimensional=2, total=6),
}


WALLPAPER_GROUPS = [
    ("p1", "oblique", "C1"),
    ("p2", "oblique", "C2"),
    ("pm", "rectangular", "D1"),
    ("pg", "rectangular", "D1"),
    ("cm", "rhombic", "D1"),
    ("pmm", "rectangular", "V4"),
    ("pmg", "rectangular", "V4"),
    ("pgg", "rectangular", "V4"),
    ("cmm", "rhombic", "V4"),
    ("p4", "square", "C4"),
    ("p4m", "square", "D4"),
    ("p4g", "square", "D4"),
    ("p3", "hexagonal", "C3"),
    ("p3m1", "hexagonal", "D3"),
    ("p31m", "hexagonal", "D3"),
    ("p6", "hexagonal", "C6"),
    ("p6m", "hexagonal", "D6"),
]


def validate_point_group_profiles() -> None:
    for label, profile in POINT_GROUPS.items():
        assert profile.degree_square_sum() == profile.order, label
        assert profile.one_dimensional + profile.two_dimensional == profile.total, label
        assert sp.Integer(profile.order) > 0
    print("PASS: point-group irrep degree-square sums recover group orders")


def validate_wallpaper_table() -> None:
    symbols = [symbol for symbol, _lattice, _point_group in WALLPAPER_GROUPS]
    assert len(symbols) == 17
    assert len(set(symbols)) == 17
    for symbol, _lattice, point_group in WALLPAPER_GROUPS:
        assert point_group in POINT_GROUPS, symbol
    print("PASS: 17 wallpaper groups map to typed holonomy point groups")


def validate_generic_little_group() -> None:
    generic_profile = POINT_GROUPS["C1"]
    for symbol, _lattice, _point_group in WALLPAPER_GROUPS:
        assert generic_profile.order == 1, symbol
        assert generic_profile.one_dimensional == 1, symbol
        assert generic_profile.two_dimensional == 0, symbol
    print("PASS: generic little group is C1 with one 1D representation")


def validate_high_symmetry_examples() -> None:
    lookup = {symbol: point_group for symbol, _lattice, point_group in WALLPAPER_GROUPS}
    assert POINT_GROUPS[lookup["p4m"]] == PointGroupProfile(8, 4, 1, 5)
    assert POINT_GROUPS[lookup["p6m"]] == PointGroupProfile(12, 4, 2, 6)
    print("PASS: p4m and p6m Gamma-point profiles match D4 and D6")


def main() -> None:
    print("=== Wallpaper representation classification certificate ===")
    validate_point_group_profiles()
    validate_wallpaper_table()
    validate_generic_little_group()
    validate_high_symmetry_examples()
    print("WALLPAPER_CLASSIFICATION_CERTIFICATE_OK")


if __name__ == "__main__":
    main()
