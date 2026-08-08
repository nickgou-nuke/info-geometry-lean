import sympy as sp

lean_code = """import Mathlib
import proofs.SplitOctonionTrialityCore

open SplitOctonion
open SplitOctonionNorm44
open SplitOctonionTrialityCore

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

"""

lean_code += "lemma left_alternative_basis (i j k : Fin 8) : (basis i) * ((basis j) * (basis k)) + ((basis i) * (basis j)) * (basis k) = 0 := by\n"
lean_code += "  fin_cases i <;> fin_cases j <;> fin_cases k\n"
lean_code += "  all_goals { dsimp [basis, smul_def, add_def, sub_def, neg_def, mul_def]; ring }\n"

with open("proofs/TestBasisExt.lean", "w") as f:
    f.write(lean_code)
