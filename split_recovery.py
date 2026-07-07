import os

chunk1 = "agent_memory_recovery/PrimeCantorTiltFockNilpotents.lean/2026-07-06_03-44-36_3b5b43b8.lean"
chunk2 = "agent_memory_recovery/PrimeCantorTiltFockNilpotents.lean/2026-07-06_03-44-54_3b5b43b8.lean"

with open(chunk1, "r") as f:
    c1_lines = f.read().splitlines()

with open(chunk2, "r") as f:
    c2_lines = f.read().splitlines()

# The first file goes up to line 348 (index 347)
core_lines = c1_lines[:348]
core_lines.append("end InfoGeometry.Arithmetic.PrimeCantorTiltFockNilpotents")

# Supergraded Closure (lines 349 to 479, indices 348 to 478)
sgc_lines = [
    "import Mathlib",
    "",
    "namespace InfoGeometry.OperatorAlgebra.SupergradedClosure",
    ""
] + c1_lines[348:479] + ["", "end InfoGeometry.OperatorAlgebra.SupergradedClosure"]

# Bott Periodic Induction (lines 480 to 531)
bott_lines = [
    "import Mathlib",
    "",
    "namespace InfoGeometry.OperatorAlgebra.BottPeriodicInduction",
    ""
] + c1_lines[479:531] + ["", "end InfoGeometry.OperatorAlgebra.BottPeriodicInduction"]

# Recursive Supercharge (lines 532 to 800, plus chunk 2 without the overlap)
rec_lines = [
    "import Mathlib",
    "import InfoGeometry.OperatorAlgebra.SupergradedClosure",
    "",
    "namespace InfoGeometry.OperatorAlgebra.RecursiveSupercharge",
    "open InfoGeometry.OperatorAlgebra.SupergradedClosure",
    ""
] + c1_lines[531:-1] # skip the very last line which is truncated

# Chunk 2 overlaps the last line of chunk 1. Let's find the overlap.
overlap_str = "    SupergradedClosureAt (R := A × B) (QA, QB) (QAsharp, QBsharp) := by"
overlap_idx = c2_lines.index(overlap_str)
c2_remainder = c2_lines[overlap_idx:]

rec_lines += c2_remainder + ["", "end InfoGeometry.OperatorAlgebra.RecursiveSupercharge"]

def write_file(path, lines):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")

write_file("lean/InfoGeometry/Arithmetic/PrimeCantorTiltFockNilpotents.lean", core_lines)
write_file("lean/InfoGeometry/OperatorAlgebra/SupergradedClosure.lean", sgc_lines)
write_file("lean/InfoGeometry/OperatorAlgebra/BottPeriodicInduction.lean", bott_lines)
write_file("lean/InfoGeometry/OperatorAlgebra/RecursiveSupercharge.lean", rec_lines)

print("Split completed successfully.")
