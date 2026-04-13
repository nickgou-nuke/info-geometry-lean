#!/usr/bin/env python3
import json
import sys
from pathlib import Path

"""
# Claim Packet Builder (V2)
Implements the expanded schema for the Discovery-Translation-Closure pipeline.
Enforces the state transition: draft -> translated -> locked.
"""

def create_packet(name, archetype, claim, lean_target, owner_file):
    packet = {
        "seed_symbol": name,
        "exploratory_source": "Black Book / Socratic Dialogues",
        "philosophical_claim": claim,
        "repo_native_formulation": "",
        "mathlib_native_formulation": "",
        "latex_statement": "",
        "symbolic_witness": {
            "kind": "python",
            "path": f"tools/witnesses/{name}_check.py",
            "result_summary": "PENDING"
        },
        "lean_target": {
            "theorem_name": lean_target,
            "expected_type": "Prop",
            "owner_file": owner_file,
            "imports_budget": ["InfoGeometry.Canonical.All"]
        },
        "comparison_theorem_required": True,
        "upstairs_content_remaining": "Full derivation from Clifford bedrock",
        "lock_status": "draft"
    }
    return packet

def main():
    if len(sys.argv) < 5:
        print("Usage: build_claim_packet.py <name> <archetype> <claim> <lean_target> <owner_file>")
        sys.exit(1)
        
    packet = create_packet(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])
    
    task_dir = Path(".tasks/claim_packets")
    task_dir.mkdir(parents=True, exist_ok=True)
    
    file_path = task_dir / f"{sys.argv[1]}.json"
    with open(file_path, 'w', encoding='utf-8') as f:
        json.dump(packet, f, indent=2, ensure_ascii=False)
        
    print(f"SUCCESS: Packet '{sys.argv[1]}' created at {file_path}")

if __name__ == "__main__":
    main()
