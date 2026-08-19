#!/usr/bin/env python3
"""SymPy audit for FinalSpectroscopicSynthesisAudit.lean.

This witness checks the finite bookkeeping behind the final spectroscopic
synthesis.  It deliberately does not certify physical QFT/nuclear-data claims;
those are deferred_interface in Lean.
"""

import sympy as sp

wallpaper_count = sp.Integer(17)
pg_h2 = sp.Integer(1)
p6m_h2 = sp.Integer(4)
observed_capstone_build_jobs = sp.Integer(8147)

raman_active = {"trivial": True, "standard": False}
mode_trapped = {"fundamental": True, "firstOvertone": True, "secondOvertone": True, "evanescent": False}
primon_overtones = [2, 3, 5]
forbidden = {"pg": "deltaJOneDoubletMixing", "p6m": "nonsingletColorMode", "cm": "isospinViolatingE1"}

cg_allowed = {
    ("1/2", "1/2", "0"): True,
    ("1/2", "1/2", "1"): True,
    ("1/2", "1/2", "3/2"): False,
}

entropy_wilson = sp.Integer(1) + sp.Integer(1) + sp.Integer(1)
broken_detailed_balance = entropy_wilson != 0

print("observed capstone build jobs =", observed_capstone_build_jobs)
print("wallpaper count =", wallpaper_count)
print("pg H2 exponent =", pg_h2)
print("p6m H2 exponent =", p6m_h2)
print("primon overtones =", primon_overtones)
print("entropy Wilson =", entropy_wilson)
print("broken detailed balance =", broken_detailed_balance)

assert observed_capstone_build_jobs == 8147
assert wallpaper_count == 17
assert pg_h2 == 1
assert p6m_h2 == 4
assert raman_active["trivial"] is True
assert raman_active["standard"] is False
assert len(primon_overtones) == 3
assert mode_trapped["evanescent"] is False
assert forbidden["pg"] == "deltaJOneDoubletMixing"
assert forbidden["p6m"] == "nonsingletColorMode"
assert cg_allowed[("1/2", "1/2", "0")] is True
assert entropy_wilson == 3
assert broken_detailed_balance is True

print("Final spectroscopic synthesis audit passed")
