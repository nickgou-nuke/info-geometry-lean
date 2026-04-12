#!/usr/bin/env python3
import sys
import json
import jsonschema
from pathlib import Path
from datetime import datetime

"""
# Spire Shadow Absorption (Residue Quarantine - Lineage Edition)
Implements recursive alchemy: split a failed proof into Gold (Proven Core) 
and Slag (Frontier Residue). Returns the slag to the Athanor and keeps the gold.
"""

SCHEMA_PATH = Path("tools/schema/rubedo_residue_packet.json")

def absorb_failure(packet_data):
    """
    Implements the Law of Lineage Preservation.
    Splits the failure into Conserved Proof Matter and Unresolved Residue.
    """
    # 1. Validate against the Rubedo Schema
    if SCHEMA_PATH.exists():
        with open(SCHEMA_PATH, "r") as f:
            schema = json.load(f)
        try:
            jsonschema.validate(instance=packet_data, schema=schema)
        except jsonschema.exceptions.ValidationError as e:
            print(f"Warning: Packet validation failed. Proceeding with Best Effort. Error: {e.message}")
    
    task_id = packet_data.get('taskId', 'unknown')
    proven_core = packet_data.get('proven_core', [])
    frontier = packet_data.get('frontier_residue', {})
    
    residue_log = Path("docs/black_books/residue_shadow.md")
    lineage_log = Path("docs/policy/lineage_skeleton.md")
    
    timestamp = datetime.now().isoformat()
    
    # 2. Extract and Save the Gold (Proven Core)
    if proven_core:
        core_fragment = f"""
## Conserved Core: {task_id} ({timestamp})
- **Status**: Stabilized Strata
- **Verified Tactics**:
{json.dumps(proven_core, indent=2)}
---
"""
        with open(lineage_log, "a") as f:
            f.write(core_fragment)
        print(f"RESIDUE: Gold (Proven Core) extracted to {lineage_log}.")

    # 3. Extract and Return the Slag (Frontier Residue)
    slag_fragment = f"""
## Frontier Residue: {task_id} ({timestamp})
- **The Obstruction**: 
```text
{frontier.get('error_logs', 'No logs available')}
```
- **Refinement Context**: {frontier.get('obstruction', 'Unknown obstruction')}
- **Suggested Refinement**: {frontier.get('suggested_refinement', 'Return to Nigredo for symbolic re-processing.')}
---
"""
    with open(residue_log, "a") as f:
        f.write(slag_fragment)
    
    print(f"RESIDUE: Slag (Frontier Residue) returned to {residue_log}.")
    print("RECURSIVE LOOP: Ascent preserved. The kernel breathes.")

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 residue_quarantine.py <residue_packet.json>")
        sys.exit(1)
    
    packet_path = Path(sys.argv[1])
    if not packet_path.exists():
        print(f"Error: Packet {packet_path} not found.")
        sys.exit(1)
        
    with open(packet_path, "r") as f:
        packet = json.load(f)
        
    absorb_failure(packet)

if __name__ == "__main__":
    main()
