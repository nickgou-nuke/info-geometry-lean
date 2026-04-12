#!/usr/bin/env python3
import sys
import json
from pathlib import Path
from datetime import datetime

"""
# Spire Shadow Absorption (Residue Quarantine)
Implements the recursive loop: Failed Formalization -> Symbolic Reservoir.
Captures the obstruction that killed a proof and stores it as 'Nigredo' ore.
"""

def absorb_failure(task_path, error_logs):
    """Refactors a failure into a symbolic fragment for future Forge runs."""
    task_path = Path(task_path)
    if not task_path.exists():
        print(f"Error: Task {task_path} not found.")
        sys.exit(1)

    with open(task_path, "r") as f:
        task = json.load(f)

    residue_file = Path("docs/black_books/residue_shadow.md")
    
    timestamp = datetime.now().isoformat()
    
    fragment = f"""
## Residue: {task['theoremName']} ({timestamp})
- **Task ID**: {task['taskId']}
- **Original Bridge**: {task.get('bridge_claim', 'Unknown')}
- **The Obstruction**: 
```text
{error_logs}
```
- **Analysis**: This formal target failed Rubedo-closure. It has been returned to the symbolic reservoir for Nigredo-reprocessing. 
- **Refinement Hint**: isolate the specific obstruction shown above and propose a new bridge state.
---
"""
    
    with open(residue_file, "a") as f:
        f.write(fragment)
    
    print(f"SUCCESS: Failure absorbed into {residue_file}. The symbol returns to shadow.")

def main():
    if len(sys.argv) < 3:
        print("Usage: python3 residue_quarantine.py <task_json> <error_string>")
        sys.exit(1)
    
    task_json = sys.argv[1]
    # Simple way to pass multi-line error: read from stdin or pass a single quoted string
    error = sys.argv[2]
    
    absorb_failure(task_json, error)

if __name__ == "__main__":
    main()
