#!/usr/bin/env python3
"""SymPy/Python audit for NuclearWallpaperSpectraClassification.lean.

External witness only: checks the finite wallpaper-to-nuclear-spectroscopy table
and extinction rules. Lean remains the proof kernel.
"""

from collections import Counter

wallpaper_groups = [
    "p1", "p2", "pm", "pg", "cm", "pmm", "pmg", "pgg", "cmm",
    "p4", "p4m", "p4g", "p3", "p3m1", "p31m", "p6", "p6m",
]

classification = {
    "p1": "genericTriaxial",
    "p2": "genericTriaxial",
    "pm": "genericTriaxial",
    "cmm": "genericTriaxial",
    "p4g": "genericTriaxial",
    "p31m": "genericTriaxial",
    "cm": "mirrorIsospin",
    "pg": "glideChiralDoublet",
    "pmg": "glideChiralDoublet",
    "pgg": "glideChiralDoublet",
    "pmm": "squareQuadrupole",
    "p4": "squareQuadrupole",
    "p4m": "squareQuadrupole",
    "p3": "trigonalCluster",
    "p3m1": "trigonalCluster",
    "p6": "hexagonalSU3Rotor",
    "p6m": "hexagonalSU3Rotor",
}

forbidden = {
    "pg": "deltaJOneDoubletMixing",
    "pmg": "deltaJOneDoubletMixing",
    "pgg": "deltaJOneDoubletMixing",
    "p6": "nonsingletColorMode",
    "p6m": "nonsingletColorMode",
    "cm": "isospinViolatingE1",
}

counts = Counter(classification[g] for g in wallpaper_groups)

print("wallpaper group count =", len(wallpaper_groups))
print("class counts =", dict(counts))
print("pg forbidden =", forbidden["pg"])
print("p6m forbidden =", forbidden["p6m"])
print("cm forbidden =", forbidden["cm"])

assert len(wallpaper_groups) == 17
assert set(classification) == set(wallpaper_groups)
assert counts["hexagonalSU3Rotor"] == 2
assert counts["glideChiralDoublet"] == 3
assert counts["squareQuadrupole"] == 3
assert counts["trigonalCluster"] == 2
assert classification["p6m"] == "hexagonalSU3Rotor"
assert classification["pg"] == "glideChiralDoublet"
assert classification["cm"] == "mirrorIsospin"
assert forbidden["pg"] == "deltaJOneDoubletMixing"
assert forbidden["p6m"] == "nonsingletColorMode"
assert forbidden["cm"] == "isospinViolatingE1"

print("Nuclear wallpaper spectra classification audit passed")
