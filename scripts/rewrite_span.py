import re

with open("lean/InfoGeometry/Canonical/H3ZornF4BasisExactSpan.lean", "r") as f:
    text = f.read()

text = text.replace("set_option maxHeartbeats 10000000\n\n", "")

proof_start = """theorem native_pivot_certificate (i j : Fin 52) :
    f4ActionMatrix j (f4ActionPivot i) =
      if j = i then (f4ActionPivotValue i : ℝ) else 0 := by
"""
proof_body = "  revert j\n  fin_cases i\n"
for i in range(52):
    proof_body += f"  · intro j; fin_cases j <;>\n      norm_num [f4ActionMatrix, f4ActionPivot, f4ActionPivotValue,\n        f4BasisActionCoordinateMatrix, f4BasisActionCoordinate,\n        f4Basis, h3ZornJordanInnerDerivation, jordanLmul,\n        candidateJordanMul, H3Zorn.T, H3Zorn.traceBilin,\n        H3Zorn.crossProduct, H3Zorn.adjointQuad,\n        H3Zorn.linearTrace, h3ZornCoordinateBasis,\n        h3ZornCoordinate,\n        h3_diag₁, h3_diag₂, h3_diag₃,\n        h3_off₁₂, h3_off₂₃, h3_off₃₁, zorn_basis,\n        ZornVectorMatrix.norm, ZornVectorMatrix.trace,\n        ZornVectorMatrix.mul, ZornVectorMatrix.conj,\n        ZornVectorMatrix.add, ZornVectorMatrix.sub,\n        ZornVectorMatrix.neg, ZornVectorMatrix.smul,\n        ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross,\n        Fin.sum_univ_three] <;> ring\n"

old_proof_pattern = r"theorem native_pivot_certificate[\s\S]*?ring\n"
text = re.sub(old_proof_pattern, proof_start + proof_body, text)

with open("lean/InfoGeometry/Canonical/H3ZornF4BasisExactSpan.lean", "w") as f:
    f.write(text)

