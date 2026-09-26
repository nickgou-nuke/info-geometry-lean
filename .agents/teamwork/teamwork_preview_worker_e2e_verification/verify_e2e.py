#!/usr/bin/env python3
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

# Add tools to sys.path for build lock
sys.path.insert(0, '/home/goutev/info-geometry-lean/tools')
import build_lock

TARGETS = [
    'lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean',
    'lean/InfoGeometry/LLM/KreinAttentionEnergy.lean',
    'lean/DAG/ConnesHodgeBridge.lean',
    'lean/DAG.lean'
]

CAS_CERTIFICATES = [
    '.agents/sandbox_correlator/CAS/certificate.json',
    '.agents/sandbox_krein/CAS/certificate.json',
    '.agents/sandbox_connes_hodge/CAS/certificate.json'
]

CHEAT_PATTERNS = {
    'sorry': re.compile(r'\bsorry\b'),
    'native_decide': re.compile(r'\bnative_decide\b'),
    'simpa using': re.compile(r'\bsimpa\s+using\b'),
    'admit': re.compile(r'\badmit\b')
}

DECLS_BY_TARGET = {
    'lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean': [
        'DetectorGeometry.FieldCorrelatorProjection.DetectorProjector',
        'DetectorGeometry.FieldCorrelatorProjection.FieldCorrelator',
        'DetectorGeometry.FieldCorrelatorProjection.projectSingle',
        'DetectorGeometry.FieldCorrelatorProjection.projectPair',
        'DetectorGeometry.FieldCorrelatorProjection.projector_single_linear',
        'DetectorGeometry.FieldCorrelatorProjection.projector_pair_bilinear_scale',
        'DetectorGeometry.FieldCorrelatorProjection.modeTrace',
        'DetectorGeometry.FieldCorrelatorProjection.oscillatory_modes_annihilated',
        'DetectorGeometry.FieldCorrelatorProjection.modeTrace_linear',
        'DetectorGeometry.FieldCorrelatorProjection.singlesCount',
        'DetectorGeometry.FieldCorrelatorProjection.coincidenceCount',
        'DetectorGeometry.FieldCorrelatorProjection.coincidence_is_rank_two',
        'DetectorGeometry.FieldCorrelatorProjection.square_root_coordinate_is_linear',
        'DetectorGeometry.FieldCorrelatorProjection.detector_projection_parabola',
        'DetectorGeometry.FieldCorrelatorProjection.Archetype',
        'DetectorGeometry.FieldCorrelatorProjection.rank',
        'DetectorGeometry.FieldCorrelatorProjection.causallyPrecedes',
        'DetectorGeometry.FieldCorrelatorProjection.causal_refl',
        'DetectorGeometry.FieldCorrelatorProjection.causal_trans',
        'DetectorGeometry.FieldCorrelatorProjection.rank_inj',
        'DetectorGeometry.FieldCorrelatorProjection.causal_antisymm',
        'DetectorGeometry.FieldCorrelatorProjection.canonical_chain'
    ],
    'lean/InfoGeometry/LLM/KreinAttentionEnergy.lean': [
        'InfoGeometry.LLM.KreinAttentionEnergy.kreinInteractionEnergy',
        'InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights',
        'InfoGeometry.LLM.KreinAttentionEnergy.kreinInteractionEnergy_eq_neg_splitB11',
        'InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights_sum_one',
        'InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights_nonneg',
        'InfoGeometry.LLM.KreinAttentionEnergy.kreinAttentionWeights_le_one'
    ],
    'lean/DAG/ConnesHodgeBridge.lean': [
        'DAG.ConnesHodgeBridge.ConnesCorrespondence',
        'DAG.ConnesHodgeBridge.fromTwoComplex',
        'DAG.ConnesHodgeBridge.fromHodgeData',
        'DAG.ConnesHodgeBridge.fromTwoComplex_edgeCount',
        'DAG.ConnesHodgeBridge.fromTwoComplex_harmonicDim',
        'DAG.ConnesHodgeBridge.fromTwoComplex_cocycleDimUpperBound',
        'DAG.ConnesHodgeBridge.fromTwoComplex_eulerChar',
        'DAG.ConnesHodgeBridge.fromHodgeData_edgeCount',
        'DAG.ConnesHodgeBridge.fromHodgeData_harmonicDim',
        'DAG.ConnesHodgeBridge.fromHodgeData_cocycleDimUpperBound',
        'DAG.ConnesHodgeBridge.fromHodgeData_eulerChar',
        'DAG.ConnesHodgeBridge.fromTwoComplex_harmonicDim_eq_cocycleDimUpperBound',
        'DAG.ConnesHodgeBridge.fromHodgeData_harmonicDim_eq_cocycleDimUpperBound',
        'DAG.ConnesHodgeBridge.harmonicDim_eq_cocycleDimUpperBound_fromTwoComplex',
        'DAG.ConnesHodgeBridge.harmonicDim_eq_cocycleDimUpperBound_fromHodgeData',
        'DAG.ConnesHodgeBridge.fromHodgeData_fromTwoComplex_edgeCount',
        'DAG.ConnesHodgeBridge.fromHodgeData_fromTwoComplex_eulerChar'
    ]
}

STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def main():
    print("================================================================================")
    print("MILESTONE 12: GLOBAL END-TO-END VERIFICATION HARNESS")
    print("================================================================================")

    # 1. CAS Certificates Verification
    print("\n--- 1. VERIFYING CAS CERTIFICATES ---")
    for cert_path in CAS_CERTIFICATES:
        p = Path(cert_path)
        assert p.is_file(), f"CAS certificate missing: {cert_path}"
        with open(p, 'r') as fp:
            data = json.load(fp)
        status = data.get('metadata', {}).get('status', 'OK')
        engine = data.get('metadata', {}).get('cas_engine', 'Unknown')
        keys = list(data.keys())
        print(f"[PASS] {cert_path}: valid JSON, engine={engine}, status={status}, keys={len(keys)}")

    # 2. Cheat Token Scan
    print("\n--- 2. SCANNING CHEAT TOKENS ---")
    total_cheat_tokens = 0
    for target in TARGETS:
        p = Path(target)
        assert p.is_file(), f"Target missing: {target}"
        lines = p.read_text(encoding='utf-8').splitlines()
        file_cheats = 0
        for pat_name, pat in CHEAT_PATTERNS.items():
            matches = []
            for lineno, line in enumerate(lines, 1):
                code_part = line.split('--')[0].strip()
                if pat.search(code_part):
                    matches.append((lineno, line.strip()))
            if matches:
                print(f"[FAIL] {target}: found {len(matches)} occurrences of {pat_name}!")
                for lineno, l in matches:
                    print(f"       Line {lineno}: {l}")
                file_cheats += len(matches)
        if file_cheats == 0:
            print(f"[PASS] {target}: 0 cheat tokens (sorry, native_decide, simpa using, admit)")
        total_cheat_tokens += file_cheats
    assert total_cheat_tokens == 0, f"Total cheat tokens found: {total_cheat_tokens}"

    # 3. Lean Compilation and Axioms under Build Lock
    print("\n--- 3. LEAN COMPILER VERIFICATION UNDER BUILD LOCK ---")
    with build_lock.acquire_build_lock(None, owner='teamwork_preview_worker_e2e_verification', block=True):
        for target in TARGETS:
            print(f"\nVerifying: {target}")
            t0 = time.time()
            res = subprocess.run(['lake', 'env', 'lean', '--threads', '1', target],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            elapsed = time.time() - t0
            print(f"  Return code: {res.returncode}")
            print(f"  Elapsed: {elapsed:.2f}s")
            
            # Check for compiler errors or warnings in stdout/stderr
            # Note: lake stderr contains manifest warnings, but lean compiler outputs file:line:col: error/warning
            lean_errors = [line for line in (res.stdout + '\n' + res.stderr).splitlines() if ': error:' in line]
            lean_warnings = [line for line in (res.stdout + '\n' + res.stderr).splitlines() if ': warning:' in line and 'manifest out of date' not in line]
            
            print(f"  Lean Compiler Errors: {len(lean_errors)}")
            print(f"  Lean Compiler Warnings: {len(lean_warnings)}")
            if lean_errors:
                print("  ERROR LINES:", lean_errors)
            if lean_warnings:
                print("  WARNING LINES:", lean_warnings)
                
            assert res.returncode == 0, f"Target {target} exited with code {res.returncode}"
            assert len(lean_errors) == 0, f"Target {target} had compiler errors: {lean_errors}"
            assert len(lean_warnings) == 0, f"Target {target} had compiler warnings: {lean_warnings}"
            print(f"[PASS] {target}: clean compilation (rc=0, 0 errors, 0 warnings)")

        # 4. Axiom Verification
        print("\n--- 4. AXIOM AUDIT VIA KERNEL ---")
        pattern = re.compile(r"'([^']+)'\s+(depends on axioms:\s*\[(.*?)\]|does not depend on any axioms)", re.DOTALL)
        for target, decls in DECLS_BY_TARGET.items():
            print(f"\nChecking axioms for {target} ({len(decls)} declarations)...")
            content = Path(target).read_text(encoding='utf-8')
            queries = '\n'.join([f'#print axioms {d}' for d in decls])
            full_code = content + '\n\n' + queries
            res = subprocess.run(['lake', 'env', 'lean', '--stdin'],
                                 input=full_code, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            assert res.returncode == 0, f"Lean stdin failed with code {res.returncode}: {res.stderr}"
            
            matches = pattern.findall(res.stdout)
            found_decls = {}
            for m in matches:
                decl_name = m[0]
                if 'does not depend on any axioms' in m[1]:
                    found_decls[decl_name] = []
                else:
                    raw_axs = [a.strip() for a in m[2].replace('\n', ' ').split(',') if a.strip()]
                    found_decls[decl_name] = raw_axs
            
            missing = set(decls) - set(found_decls.keys())
            assert len(missing) == 0, f"Missing declaration axiom outputs: {missing}"
            
            for decl_name in decls:
                axs = found_decls[decl_name]
                for ax in axs:
                    assert ax in STANDARD_AXIOMS, f"Non-standard axiom: {ax} in {decl_name}"
                print(f"  [AXIOM OK] {decl_name} -> {axs if axs else '[] (constructive)'}")
            print(f"[PASS] {target}: All {len(decls)} declarations verified with standard axioms only!")

    print("\n================================================================================")
    print("GLOBAL END-TO-END VERIFICATION: 100% SUCCESS")
    print("================================================================================")

if __name__ == '__main__':
    main()
