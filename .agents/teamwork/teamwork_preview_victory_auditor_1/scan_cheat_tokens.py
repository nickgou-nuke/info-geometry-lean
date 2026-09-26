import sys
import re

files_to_scan = [
    "lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean",
    "lean/InfoGeometry/LLM/KreinAttentionEnergy.lean",
    "lean/DAG/ConnesHodgeBridge.lean",
    "lean/DAG.lean",
    "lean/DAG/TwoComplexFunctor.lean",
    "lean/InfoGeometry/LLM/KreinEuclideanComparison.lean"
]

banned_patterns = [
    r"\bsorry\b",
    r"\badmit\b",
    r"\bnative_decide\b",
    r"\bsimpa\s+using\b",
    r"\bunsafe\b",
    r"\baxiom\b"
]

violations = []

for file_path in files_to_scan:
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            lines = f.readlines()
        
        for line_no, line in enumerate(lines, start=1):
            # Strip comments for inspection, but keep track of raw line
            code_part = line.split("--")[0]
            for pattern in banned_patterns:
                if re.search(pattern, code_part):
                    violations.append((file_path, line_no, pattern, line.strip()))
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        sys.exit(1)

print(f"Scanned {len(files_to_scan)} files.")
if violations:
    print(f"VIOLATIONS FOUND ({len(violations)}):")
    for v in violations:
        print(f"  {v[0]}:{v[1]} matched {v[2]} -> {v[3]}")
    sys.exit(1)
else:
    print("Zero cheat tokens detected. All files are CLEAN.")
