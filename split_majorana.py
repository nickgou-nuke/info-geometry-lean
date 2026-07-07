import os

rec_file = "agent_memory_recovery/PrimeMajoranaBitFlip.lean/2026-07-06_03-42-55_d55d68f8.lean"

with open(rec_file, "r") as f:
    lines = f.read().splitlines()

part1 = lines[:88] + ["", "end InfoGeometry.Arithmetic.PrimeMajoranaBitFlip"]

part2 = [
    "import Mathlib",
    "import InfoGeometry.Meta.SocketTarget",
    "import InfoGeometry.Arithmetic.PrimeMajoranaBitFlip",
    "",
    "namespace InfoGeometry.Arithmetic.PrimeMajoranaBitFlip",
    ""
] + lines[91:180] + ["", "end InfoGeometry.Arithmetic.PrimeMajoranaBitFlip"]

def write_file(path, lines):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")

write_file("lean/InfoGeometry/Arithmetic/PrimeMajoranaBitFlip.lean", part1)
write_file("lean/InfoGeometry/Arithmetic/PrimeMajoranaCARGate.lean", part2)

print("Split completed successfully.")
