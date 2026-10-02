#!/usr/bin/env python3
import sys
from pathlib import Path
REPO_ROOT = Path("/home/goutev/info-geometry-lean")
sys.path.insert(0, str(REPO_ROOT))

import subprocess
from tools.build_lock import acquire_build_lock

TARGET = "/home/goutev/info-geometry-lean/.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean"

# Declarations to check
DECLS = [
    "weakNilpotentLane_sq_eq_zero",
    "weakA_sq_readout",
    "weakA_pow_three",
    "weakA_cubic_eq_two_smul_square",
    "weakDrazinInverse_isDrazin",
    "weakDrazinInverse_isWeak",
    "weakWildInverse_isWeak",
    "weakWildInverse_ne_Drazin",
    "weakWildInverse_not_commuting",
    "weakPolynomialInverse_isWeak",
    "weakPolynomialInverse_isCommuting",
    "weakPolynomialInverseUnit",
    "weakPolynomialInverse_ne_Drazin",
    "weakSouriauFrame_formula_eq_polynomial",
    "weakProjectiveInverse_isWeak",
    "weakProjectiveInverse_BA_readout",
    "weakProjectiveInverse_BA_idempotent",
    "weakCommutingInverse_isCommuting",
    "weakPermutation_sq_eq_one",
    "weakPermutationUnit",
    "unitConj_mul",
    "unitConj_pow",
    "unitConj_isWeakDrazin",
    "weak_conjugated_polynomial_inverse_isWeak"
]

code = f'''
import InfoGeometry.Canonical.CampbellMeyerWeakDrazin
open InfoGeometry.Canonical.CampbellMeyerWeakDrazin
'''

for d in DECLS:
    code += f"#print axioms {d}\n"

test_file = Path("/home/goutev/info-geometry-lean/.agents/challenger_weak_drazin_1/tmp/axiom_check.lean")
test_file.write_text(code, encoding="utf-8")

with acquire_build_lock(None, "challenger_axiom_check", block=True):
    res = subprocess.run(["lake", "env", "lean", str(test_file)], capture_output=True, text=True, cwd=str(REPO_ROOT))

test_file.unlink()

print("STDOUT:")
print(res.stdout)
print("STDERR:")
print(res.stderr)
print("RC:", res.returncode)

lines = res.stdout.splitlines()
contains_cheat = False
for line in lines:
    if "Lean.ofReduceBool" in line:
        print("[!] CHEAT DETECTED: Lean.ofReduceBool found:", line)
        contains_cheat = True
    if "sorry" in line:
        print("[!] CHEAT DETECTED: sorry found:", line)
        contains_cheat = True

if not contains_cheat and res.returncode == 0:
    print("[PASS] Zero cheats, zero sorry, zero Lean.ofReduceBool found across all declarations!")
