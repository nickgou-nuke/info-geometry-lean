#!/usr/bin/env python3
import os
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "lean" / "InfoGeometry"
OUTPUT_FILE = ROOT / "artifacts" / "training" / "deepseek_ground_truth.jsonl"
HARVESTER_LEAN = ROOT / "lean" / "DAG" / "GroundTruthHarvester.lean"

LOG_FILE = ROOT / "artifacts" / "training" / "harvest_errors.log"
FAILED_FILES_FILE = ROOT / "artifacts" / "training" / "failed_files.json"

def harvest_file(lean_file, log_f):
    print(f"Harvesting {lean_file}...", flush=True)
    try:
        harvester_exe = ROOT / ".lake" / "build" / "bin" / "groundTruthHarvester"
        if not harvester_exe.exists():
            subprocess.run(["lake", "build", "groundTruthHarvester"], check=True, cwd=ROOT)

        cmd = ["lake", "env", str(harvester_exe), str(lean_file)]
        # Add a 60s timeout per file to prevent hangs
        result = subprocess.run(cmd, capture_output=True, text=True, check=True, cwd=ROOT, timeout=60)

        # Per-file deduplication: keep the longest tactic for each (goalBefore, goalAfter) pair
        raw_steps = result.stdout.strip().split("\n")
        best_steps = {} # (goalBefore, goalAfter) -> best_tactic
        
        for step_json in raw_steps:
            if not step_json.strip(): continue
            try:
                step = json.loads(step_json)
                key = (step['goalBefore'], step['goalAfter'])
                tactic = step['tactic'].strip()
                if key not in best_steps or len(tactic) > len(best_steps[key]):
                    best_steps[key] = tactic
            except: continue
            
        return best_steps
    except subprocess.TimeoutExpired:
        error_msg = f"Timeout harvesting {lean_file}\n"
        print(error_msg)
        log_f.write(error_msg + "-"*40 + "\n")
        return None
    except subprocess.CalledProcessError as e:
        error_msg = f"Error harvesting {lean_file}:\n{e.stderr}\n"
        print(error_msg)
        log_f.write(error_msg + "-"*40 + "\n")
        return None

def main():
    os.makedirs(OUTPUT_FILE.parent, exist_ok=True)
    all_steps_count = 0
    failed_files = []
    
    lean_files = sorted(list(LEAN_DIR.rglob("*.lean")))
    print(f"Found {len(lean_files)} files to harvest.")
    
    # Using 'a' mode to allow resuming or just being safer in background
    with open(OUTPUT_FILE, "w") as f, open(LOG_FILE, "w") as log_f:
        for lean_file in lean_files:
            best_steps = harvest_file(lean_file, log_f)
            if best_steps is None:
                failed_files.append(str(lean_file.relative_to(ROOT)))
                continue

            lean_file_rel = str(lean_file.relative_to(ROOT))
            module_name = lean_file_rel.replace("/", ".").replace(".lean", "")
            if module_name.startswith("lean."):
                module_name = module_name[5:]

            for (goalBefore, goalAfter), tactic in best_steps.items():
                training_row = {
                    "messages": [
                        {
                            "role": "system", 
                            "content": "You are a Lean 4 formalization expert specializing in information geometry and mathematical physics."
                        },
                        {
                            "role": "user", 
                            "content": f"Module: {module_name}\nGoal State:\n{goalBefore}\n\nWhat is the next tactic to apply?"
                        },
                        {
                            "role": "assistant", 
                            "content": tactic
                        }
                    ]
                }
                f.write(json.dumps(training_row) + "\n")
                all_steps_count += 1
            f.flush() # Ensure it's written frequently
    
    with open(FAILED_FILES_FILE, "w") as ff:
        json.dump(failed_files, ff, indent=2)
                    
    print(f"Successfully harvested {all_steps_count} tactic steps to {OUTPUT_FILE}")
    if failed_files:
        print(f"Failed to harvest {len(failed_files)} files. See {LOG_FILE} and {FAILED_FILES_FILE} for details.")

if __name__ == "__main__":
    main()
