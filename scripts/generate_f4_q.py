#!/usr/bin/env python3
import os

with open("lean/InfoGeometry/Algebra/BaezF4H3Zorn.lean") as f:
    text = f.read()

# We only need the definitions of h3_diag, h3_off, zorn_basis, f4Basis
# But we can just generate them manually in Q.

lean_code = """import Mathlib
import InfoGeometry.Algebra.BaezF4H3Zorn
import InfoGeometry.Canonical.F4ActionMatrixRationalCertificate

noncomputable section

namespace InfoGeometry.Canonical.H3ZornF4BasisExactSpan

open InfoGeometry.Algebra
open InfoGeometry.Canonical.F4ActionMatrix
open InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
open InfoGeometry.Canonical.H3ZornBasis

-- We define the exact same f4Basis over ℚ
"""
with open("lean/InfoGeometry/Canonical/H3ZornF4BasisQ.lean", "w") as f:
    f.write(lean_code)
