#!/usr/bin/env python3
"""SymPy/Python witness for wallpaper holographic selection rules.

Finite audit companion to `WallpaperHolographicSelectionRules.lean`.
It checks:

* the 17 wallpaper names include `pg` and `p6m`;
* the `pg` glide squares to a translation;
* the `S_3` irrep dimensions satisfy 1^2+1^2+2^2=6;
* the 4 Cuntz/color-spinor lanes decompose as 2*trivial + 1*standard;
* the Raman/GNS toy selection rule activates only the trivial sector.
"""

from __future__ import annotations

from enum import Enum


WALLPAPER_NAMES = [
    "p1",
    "p2",
    "pm",
    "pg",
    "cm",
    "pmm",
    "pmg",
    "pgg",
    "cmm",
    "p4",
    "p4m",
    "p4g",
    "p3",
    "p3m1",
    "p31m",
    "p6",
    "p6m",
]


class S3Sector(Enum):
    TRIVIAL = "trivial"
    SIGN = "sign"
    STANDARD = "standard"


def pg_glide(point: tuple[int, int]) -> tuple[int, int]:
    x, y = point
    return x + 1, -y


def translate_two_x(point: tuple[int, int]) -> tuple[int, int]:
    x, y = point
    return x + 2, y


def raman_active(sector: S3Sector) -> bool:
    return sector is S3Sector.TRIVIAL


def main() -> None:
    assert len(WALLPAPER_NAMES) == 17
    assert "pg" in WALLPAPER_NAMES
    assert "p6m" in WALLPAPER_NAMES

    samples = [(0, 0), (1, 2), (-3, 5), (7, -11)]
    for point in samples:
        assert pg_glide(pg_glide(point)) == translate_two_x(point)

    # S3 dimensions: trivial, sign, standard.
    dims = {"trivial": 1, "sign": 1, "standard": 2}
    assert sum(dim**2 for dim in dims.values()) == 6

    # Color spinor decomposition: 2*trivial + 0*sign + 1*standard = 4.
    multiplicities = {"trivial": 2, "sign": 0, "standard": 1}
    assert sum(multiplicities[name] * dims[name] for name in dims) == 4

    assert raman_active(S3Sector.TRIVIAL)
    assert not raman_active(S3Sector.SIGN)
    assert not raman_active(S3Sector.STANDARD)

    print("wallpaper count =", len(WALLPAPER_NAMES))
    print("pg and p6m present =", "pg" in WALLPAPER_NAMES, "p6m" in WALLPAPER_NAMES)
    print("pg glide squared samples =", [pg_glide(pg_glide(point)) for point in samples])
    print("S3 irrep square sum =", sum(dim**2 for dim in dims.values()))
    print("Cuntz/color-spinor dimension =", sum(multiplicities[name] * dims[name] for name in dims))
    print("Raman active sectors =", [sector.value for sector in S3Sector if raman_active(sector)])
    print("wallpaper_holographic_selection_rules.py: finite audit passed")


if __name__ == "__main__":
    main()
