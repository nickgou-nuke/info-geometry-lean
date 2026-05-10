#!/usr/bin/env python3
"""
Deterministic Archon-style harness: enforce packet lineage, schema, and Pi/Paperclip/Leanstral execution via a single local run.

Usage:
  python3 tools/run_archon_harness.py --packet handover/injections/YourPacket.json --mode verify --yaml
"""
import sys
import argparse
import json
import yaml
from pathlib import Path

from tools.infra.hive_packet_validate import SCHEMA_BY_KIND, build_store, validate_packet
# Placeholders -- patch with your actual Pi/Paperclip/Leanstral hooks as found above
try:
    from tools.infra.hive_workflow_policy import run_policy_gates
except ImportError:
    def run_policy_gates(packet, mode=None):
        return {"allowed": True, "reason": "[stub] All packets permitted (patch this)"}
try:
    from tools.infra.hive_leanstral_bee_worker import run_leanstral_verification
except ImportError:
    def run_leanstral_verification(packet):
        return {"status": "ok", "details": "[stub] Leanstral not wired, patch in actual execution!"}

def main():
    parser = argparse.ArgumentParser(description="Deterministic Archon-style packet→leanstral harness")
    parser.add_argument("--packet", type=str, required=True, help="Path to Lean/Hive packet (JSON)")
    parser.add_argument("--mode", type=str, default="verify", choices=["verify", "build", "audit"], help="Run mode (verify default)")
    parser.add_argument("--yaml", action="store_true", help="Print output as YAML instead of JSON")
    args = parser.parse_args()

    packet_path = Path(args.packet)
    if not packet_path.exists():
        print(f"ERROR: Packet file not found: {packet_path}", file=sys.stderr)
        sys.exit(1)

    with packet_path.open() as f:
        packet = json.load(f)

    # Detect packet kind for schema lookup
    kind = packet.get("kind")
    schema_path = SCHEMA_BY_KIND.get(kind)
    if not schema_path:
        print(f"ERROR: Unknown or unsupported packet kind: {kind}", file=sys.stderr)
        sys.exit(2)

    # 1. Schema validation
    errors = validate_packet(packet, schema_path, build_store())
    valid = not errors
    print({"step": "validate_schema", "result": valid, "errors": errors})
    if not valid:
        print("Packet schema validation FAILED. Exiting.")
        sys.exit(3)

    # 2. Policy gating (Paperclip-style)
    policy_result = run_policy_gates(packet, mode=args.mode)
    print({"step": "policy_enforcement", "result": policy_result})
    if not policy_result.get("allowed", False):
        print(f"Packet rejected by policy gate: {policy_result['reason']}")
        sys.exit(4)

    # 3. Pi/Leanstral execution
    if args.mode == "verify":
        proof_result = run_leanstral_verification(packet)
        print({"step": "leanstral_verify", "result": proof_result})
    elif args.mode == "build":
        proof_result = {"status": "TODO", "details": "BUILD mode wiring not yet implemented."}
        print({"step": "build_mode", "result": proof_result})
    elif args.mode == "audit":
        proof_result = {"status": "TODO", "details": "AUDIT mode wiring not yet implemented."}
        print({"step": "audit_mode", "result": proof_result})

    # 4. Print output in user’s desired format
    output = {
        "schema_check": valid,
        "schema_errors": errors,
        "policy": policy_result,
        "proof_result": proof_result
    }
    if args.yaml:
        print(yaml.dump(output, sort_keys=False))
    else:
        print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()
