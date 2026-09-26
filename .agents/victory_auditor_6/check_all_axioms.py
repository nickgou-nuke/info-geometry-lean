import sys, os, subprocess, re
from pathlib import Path

repo_root = Path("/home/goutev/info-geometry-lean")
sys.path.insert(0, str(repo_root))
from tools.build_lock import acquire_build_lock

targets = [
    ("lean/DAG/Dominators.lean", "DAG.Dominators"),
    ("lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean", "InfoGeometry.Canonical.CampbellMeyerWeakDrazin"),
    ("lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean", "InfoGeometry.Canonical.Hartwig1976SVDMoorePenroseBorder"),
    ("lean/DAG/DiracLaplacian.lean", "DAG.DiracLaplacian"),
    ("lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean", "InfoGeometry.Quantum.NoncommutativeFockBridge")
]

# For each target, find all theorems and defs that have proofs or axioms
for path, mod in targets:
    full_path = repo_root / path
    text = full_path.read_text()
    
    # Extract theorems/lemmas
    thms = re.findall(r"^(?:protected\s+)?(?:noncomputable\s+)?(?:theorem|lemma)\s+([A-Za-z0-9_]+)", text, re.MULTILINE)
    print(f"\n==========================================")
    print(f"Target: {mod} ({len(thms)} theorems/lemmas)")
    print(f"==========================================")
    
    # Create temporary harness file
    harness_path = repo_root / ".agents/victory_auditor_6" / f"AxiomAudit_{mod.replace('.', '_')}.lean"
    harness_content = f"import {mod}\n\n"
    for thm in thms:
        harness_content += f"#print axioms {mod}.{thm}\n"
    
    harness_path.write_text(harness_content)
    
    with acquire_build_lock(None, f"auditor6_axioms_{mod}", block=True):
        res = subprocess.run(["lake", "env", "lean", str(harness_path)], cwd=str(repo_root), capture_output=True, text=True)
        if res.returncode != 0:
            print(f"ERROR checking {mod}:\n{res.stderr}\n{res.stdout}")
            sys.exit(1)
        
        output = res.stdout
        # parse the axioms output
        # format: '<name>' depends on axioms: [axiom1, axiom2, ...] or 'does not depend on any axioms'
        lines = output.strip().splitlines()
        banned_found = False
        for line in lines:
            if "depends on axioms:" in line or "does not depend on any axioms" in line:
                print(f"  {line}")
                if "sorryAx" in line or "Lean.ofReduceBool" in line or "trustCompiler" in line:
                    print(f"  CRITICAL FAILURE: Banned axiom detected: {line}")
                    banned_found = True
        if banned_found:
            print(f"FAIL: Banned axioms detected in {mod}")
            sys.exit(1)
        else:
            print(f"PASS: All theorems in {mod} have authentic axioms.")

print("\nALL TARGET AXIOM CHECKS COMPLETED CLEANLY.")
