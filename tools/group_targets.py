import json
import os
from collections import defaultdict

with open("scratch/hive_subagent_targets.json") as f:
    targets = json.load(f)

groups = defaultdict(list)
for t in targets:
    # e.g. lean/InfoGeometry/Canonical/K0Functor.lean -> InfoGeometry/Canonical
    parts = t["target"].split('/')
    if len(parts) >= 3:
        group_name = parts[1] + "/" + parts[2]
    else:
        group_name = "root"
    groups[group_name].append(t)

for g, items in groups.items():
    print(f"{g}: {len(items)} files")
