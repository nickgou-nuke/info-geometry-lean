#!/usr/bin/env python3
import os

os.makedirs("lean/InfoGeometry/Canonical", exist_ok=True)
with open("lean/InfoGeometry/Canonical/H3ZornF4BasisPivotEvidence.lean", "w") as f:
    f.write("""import Mathlib
import InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
import InfoGeometry.Canonical.H3ZornExplicitPeirceG2Leibniz

import InfoGeometry.Canonical.F4ActionMatrixRankCertificateBridge

noncomputable section

namespace InfoGeometry.Canonical.H3ZornF4BasisExactSpan

set_option maxHeartbeats 1000000

open InfoGeometry.Algebra
open InfoGeometry.Canonical.F4ActionMatrix
open InfoGeometry.Canonical.F4ActionMatrixRationalCertificate
open InfoGeometry.Canonical.H3ZornBasis

""")
    for i in range(52):
        f.write(f"""theorem native_pivot_certificate_{i} (j : Fin 52) :
    f4ActionMatrix j (f4ActionPivot {i}) = if j = {i} then (f4ActionPivotValue {i} : ℝ) else 0 := by
  sorry

""")
