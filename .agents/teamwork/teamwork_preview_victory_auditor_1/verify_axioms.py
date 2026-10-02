import subprocess
import re
import sys
import os

sys.path.insert(0, os.path.abspath('.'))
from tools.build_lock import acquire_build_lock

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

targets = [
    {
        "file": "lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean",
        "import": "InfoGeometry.Detector.FieldCorrelatorProjection",
        "decls": [
            "DetectorGeometry.FieldCorrelatorProjection.projectSingle",
            "DetectorGeometry.FieldCorrelatorProjection.projectPair",
            "DetectorGeometry.FieldCorrelatorProjection.projector_single_linear",
            "DetectorGeometry.FieldCorrelatorProjection.projector_pair_bilinear_scale",
            "DetectorGeometry.FieldCorrelatorProjection.modeTrace",
            "DetectorGeometry.FieldCorrelatorProjection.oscillatory_modes_annihilated",
            "DetectorGeometry.FieldCorrelatorProjection.modeTrace_linear",
            "DetectorGeometry.FieldCorrelatorProjection.singlesCount",
            "DetectorGeometry.FieldCorrelatorProjection.coincidenceCount",
            "DetectorGeometry.FieldCorrelatorProjection.coincidence_is_rank_two",
            "DetectorGeometry.FieldCorrelatorProjection.square_root_coordinate_is_linear",
            "DetectorGeometry.FieldCorrelatorProjection.detector_projection_parabola",
            "DetectorGeometry.FieldCorrelatorProjection.Archetype",
            "DetectorGeometry.FieldCorrelatorProjection.rank",
            "DetectorGeometry.FieldCorrelatorProjection.causallyPrecedes",
            "DetectorGeometry.FieldCorrelatorProjection.causal_refl",
            "DetectorGeometry.FieldCorrelatorProjection.causal_trans",
            "DetectorGeometry.FieldCorrelatorProjection.rank_inj",
            "DetectorGeometry.FieldCorrelatorProjection.causal_antisymm",
            "DetectorGeometry.FieldCorrelatorProjection.canonical_chain"
        ]
    },
    {
        "file": "lean/InfoGeometry/LLM/KreinAttentionEnergy.lean",
        "import": "InfoGeometry.LLM.KreinAttentionEnergy",
        "decls": [
            "InfoGeometry.LLM.KreinAttentionEnergy.kreinInteractionEnergy",
            "InfoGeometry.LLM.KreinAttentionEnergy.kreinInteractionEnergy_eq_neg_splitB11",
            "InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights",
            "InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionHead",
            "InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights_sum_one",
            "InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights_nonneg",
            "InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights_le_one"
        ]
    },
    {
        "file": "lean/DAG/ConnesHodgeBridge.lean",
        "import": "DAG.ConnesHodgeBridge",
        "decls": [
            "DAG.ConnesHodgeBridge.ConnesCorrespondence",
            "DAG.ConnesHodgeBridge.fromTwoComplex",
            "DAG.ConnesHodgeBridge.fromHodgeData",
            "DAG.ConnesHodgeBridge.fromTwoComplex_edgeCount",
            "DAG.ConnesHodgeBridge.fromTwoComplex_harmonicDim",
            "DAG.ConnesHodgeBridge.fromTwoComplex_cocycleDimUpperBound",
            "DAG.ConnesHodgeBridge.fromTwoComplex_eulerChar",
            "DAG.ConnesHodgeBridge.fromHodgeData_edgeCount",
            "DAG.ConnesHodgeBridge.fromHodgeData_harmonicDim",
            "DAG.ConnesHodgeBridge.fromHodgeData_cocycleDimUpperBound",
            "DAG.ConnesHodgeBridge.fromHodgeData_eulerChar",
            "DAG.ConnesHodgeBridge.fromTwoComplex_harmonicDim_eq_cocycleDimUpperBound",
            "DAG.ConnesHodgeBridge.fromHodgeData_harmonicDim_eq_cocycleDimUpperBound",
            "DAG.ConnesHodgeBridge.harmonicDim_eq_cocycleDimUpperBound_fromTwoComplex",
            "DAG.ConnesHodgeBridge.harmonicDim_eq_cocycleDimUpperBound_fromHodgeData",
            "DAG.ConnesHodgeBridge.fromHodgeData_fromTwoComplex_edgeCount",
            "DAG.ConnesHodgeBridge.fromHodgeData_fromTwoComplex_eulerChar"
        ]
    }
]

total_decls = 0
violations = []

with acquire_build_lock(None, 'verify_axioms_auditor', block=True):
    for tgt in targets:
        print(f"\nVerifying axioms for {tgt['import']} ({tgt['file']}):")
        test_code_lines = [f"import {tgt['import']}"]
        for d in tgt['decls']:
            test_code_lines.append(f"#print axioms {d}")
        
        test_file = "/tmp/test_axioms_auditor.lean"
        with open(test_file, "w") as f:
            f.write("\n".join(test_code_lines) + "\n")
            
        cmd = ["lake", "env", "lean", "--threads", "1", test_file]
        res = subprocess.run(cmd, capture_output=True, text=True)
        if res.returncode != 0:
            print(f"Error compiling axiom test file for {tgt['import']}:")
            print("STDOUT:", res.stdout)
            print("STDERR:", res.stderr)
            sys.exit(1)
            
        lines = res.stdout.strip().splitlines()
        
        for line in lines:
            line_str = line.strip()
            if not line_str:
                continue
            m_none = re.search(r"'([^']+)' does not depend on any axioms", line_str)
            m_dep = re.search(r"'([^']+)' depends on axioms:\s*\[(.*)\]", line_str)
            if m_none:
                decl_name = m_none.group(1)
                total_decls += 1
                print(f"  {decl_name}: NO AXIOMS (pure)")
            elif m_dep:
                decl_name = m_dep.group(1)
                total_decls += 1
                raw_axioms = [a.strip() for a in m_dep.group(2).split(",") if a.strip()]
                non_standard = [a for a in raw_axioms if a not in STANDARD_AXIOMS]
                if non_standard:
                    violations.append((decl_name, non_standard))
                    print(f"  {decl_name}: INVALID AXIOMS -> {non_standard}")
                else:
                    print(f"  {decl_name}: VALID -> {raw_axioms}")
            else:
                print(f"  [output]: {line_str}")

print(f"\nTotal declarations checked: {total_decls}")
if violations:
    print(f"VIOLATIONS FOUND: {violations}")
    sys.exit(1)
else:
    print("ALL DECLARATIONS DEPEND EXCLUSIVELY ON STANDARD LEAN 4 KERNEL AXIOMS (0 violations).")
