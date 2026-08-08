#!/usr/bin/env python3
"""Finite witness for WallpaperNuclearSpectroscopyClassification.lean."""

from __future__ import annotations

from enum import Enum


class WallpaperGroup17(Enum):
    P1 = "p1"
    P2 = "p2"
    PM = "pm"
    PG = "pg"
    CM = "cm"
    PMM = "pmm"
    PMG = "pmg"
    PGG = "pgg"
    CMM = "cmm"
    P4 = "p4"
    P4M = "p4m"
    P4G = "p4g"
    P3 = "p3"
    P3M1 = "p3m1"
    P31M = "p31m"
    P6 = "p6"
    P6M = "p6m"


class Cluster(Enum):
    PRIMITIVE_TRIAXIAL = "primitive/triaxial"
    MIRROR_ISOSPIN = "mirror/isospin"
    GLIDE_CHIRAL = "glide/chiral"
    SQUARE_QUADRUPOLE = "square/quadrupole"
    TRIGONAL_CLUSTER = "trigonal/cluster"
    HEXAGONAL_SU3_ROTOR = "hexagonal/SU3 rotor"


class Extinction(Enum):
    NONE = "none"
    ISOSPIN_E1 = "isospin-violating E1 extinguished"
    DELTA_J1_DOUBLET = "Delta J=1 doublet mixing extinguished"
    COLOR_NONSINGLET = "non-singlet color mode extinguished"
    NON_COUNTING = "non-counting overtone extinguished"
    NON_TRIANGULAR = "non-triangular cluster mode extinguished"


ALL_GROUPS = list(WallpaperGroup17)


def nuclear_cluster(group: WallpaperGroup17) -> Cluster:
    if group in {WallpaperGroup17.P1, WallpaperGroup17.P2}:
        return Cluster.PRIMITIVE_TRIAXIAL
    if group in {WallpaperGroup17.PM, WallpaperGroup17.CM, WallpaperGroup17.CMM}:
        return Cluster.MIRROR_ISOSPIN
    if group in {WallpaperGroup17.PG, WallpaperGroup17.PMG, WallpaperGroup17.PGG, WallpaperGroup17.P4G}:
        return Cluster.GLIDE_CHIRAL
    if group in {WallpaperGroup17.PMM, WallpaperGroup17.P4, WallpaperGroup17.P4M}:
        return Cluster.SQUARE_QUADRUPOLE
    if group in {WallpaperGroup17.P3, WallpaperGroup17.P3M1, WallpaperGroup17.P31M}:
        return Cluster.TRIGONAL_CLUSTER
    if group in {WallpaperGroup17.P6, WallpaperGroup17.P6M}:
        return Cluster.HEXAGONAL_SU3_ROTOR
    raise AssertionError(group)


def extinction_rule(group: WallpaperGroup17) -> Extinction:
    if group in {WallpaperGroup17.P1, WallpaperGroup17.P2}:
        return Extinction.NONE
    if group in {WallpaperGroup17.PM, WallpaperGroup17.CM, WallpaperGroup17.CMM}:
        return Extinction.ISOSPIN_E1
    if group in {WallpaperGroup17.PG, WallpaperGroup17.PMG, WallpaperGroup17.PGG, WallpaperGroup17.P4G}:
        return Extinction.DELTA_J1_DOUBLET
    if group in {WallpaperGroup17.PMM, WallpaperGroup17.P4, WallpaperGroup17.P4M}:
        return Extinction.NON_COUNTING
    if group in {WallpaperGroup17.P3, WallpaperGroup17.P3M1, WallpaperGroup17.P31M}:
        return Extinction.NON_TRIANGULAR
    if group in {WallpaperGroup17.P6, WallpaperGroup17.P6M}:
        return Extinction.COLOR_NONSINGLET
    raise AssertionError(group)


def main() -> None:
    assert len(ALL_GROUPS) == 17
    assert nuclear_cluster(WallpaperGroup17.P6M) is Cluster.HEXAGONAL_SU3_ROTOR
    assert nuclear_cluster(WallpaperGroup17.PG) is Cluster.GLIDE_CHIRAL
    assert nuclear_cluster(WallpaperGroup17.P4M) is Cluster.SQUARE_QUADRUPOLE
    assert nuclear_cluster(WallpaperGroup17.P3M1) is Cluster.TRIGONAL_CLUSTER
    assert nuclear_cluster(WallpaperGroup17.CM) is Cluster.MIRROR_ISOSPIN

    assert extinction_rule(WallpaperGroup17.PG) is Extinction.DELTA_J1_DOUBLET
    assert extinction_rule(WallpaperGroup17.P6M) is Extinction.COLOR_NONSINGLET
    assert extinction_rule(WallpaperGroup17.CM) is Extinction.ISOSPIN_E1

    print("wallpaper groups =", len(ALL_GROUPS))
    print("p6m cluster =", nuclear_cluster(WallpaperGroup17.P6M).value)
    print("pg cluster =", nuclear_cluster(WallpaperGroup17.PG).value)
    print("p4m cluster =", nuclear_cluster(WallpaperGroup17.P4M).value)
    print("p3m1 cluster =", nuclear_cluster(WallpaperGroup17.P3M1).value)
    print("cm extinction =", extinction_rule(WallpaperGroup17.CM).value)
    print("wallpaper_nuclear_spectroscopy_classification.py: finite audit passed")


if __name__ == "__main__":
    main()
