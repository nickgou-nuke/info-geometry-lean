import os

diff_files = [
    "All.lean", "CuntzEndomorphism.lean", "FibAnyonThm2.lean", "FibAnyonThm3.lean",
    "FibAnyonThm4.lean", "FibAnyonThm5.lean", "GrandUnifiedTKK.lean", "HexagonCocycle.lean",
    "lakefile.toml", "lake-manifest.json", "lean-toolchain", "NarainMajoranaZeroModes.lean",
    "non_iso_conf3_rank32_external_audit.py", "o55_dmodule_weyl.m2", "quantum-proof-plan.md",
    "ScratchTest.lean", "setup.sh", "SplitOctonionTomitaTakesaki.lean", "temp2.lean",
    "TestAlgebra.lean", "TestIsom.lean", "Test.lean", "TestNative.lean", "test_omega.lean",
    "test_smul.lean", "TKKJordanPairData.lean", "tools/lean_graph/DumpLeanGraph.lean",
    "tools/lean_graph/ExtractGraph.lean", "TopologicalQuantumGates.lean",
    "WeylHamiltonianTopology.lean", "WittenMoebiusIndex.lean", "ZornMajoranaBraiding.lean",
    "ZornOPParavector.lean"
]

import subprocess

for f in diff_files:
    path1 = f"proofs/{f}"
    path2 = f"external_refs/auto_recovery/proofs/{f}"
    
    if os.path.exists(path1) and os.path.exists(path2):
        s1 = os.path.getsize(path1)
        s2 = os.path.getsize(path2)
        print(f"{f}: proofs= {s1} bytes, auto_recovery= {s2} bytes")
        if s2 > s1:
            print(f"  -> auto_recovery version is larger!")
            # Let's copy it over!
            subprocess.run(["cp", path2, path1])
