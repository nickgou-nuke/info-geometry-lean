import json
import os
import glob

# Load the survey analysis
with open(".agents/explorer_survey_r5_1/survey_analysis.json", "r") as f:
    survey = json.load(f)

# Create a map of module name to native_decide count
native_decide_map = {}
for entry in survey:
    if entry["native_decide_count"] > 0:
        native_decide_map[entry["module"]] = entry["native_decide_count"]

# Get all olean files and their modification times
olean_files = []
for root, dirs, files in os.walk(".lake/build/lib/lean"):
    for file in files:
        if file.endswith(".olean"):
            full_path = os.path.join(root, file)
            mtime = os.path.getmtime(full_path)
            
            # Extract module name from path
            # e.g. .lake/build/lib/lean/InfoGeometry/Canonical/PathIntegral.olean -> InfoGeometry.Canonical.PathIntegral
            rel_path = os.path.relpath(full_path, ".lake/build/lib/lean")
            module_name = rel_path.replace("/", ".").replace(".olean", "")
            
            olean_files.append({"module": module_name, "mtime": mtime})

# Sort by modification time ascending
olean_files.sort(key=lambda x: x["mtime"])

# Calculate delta t (time since previous file finished)
results = []
for i in range(1, len(olean_files)):
    delta_t = olean_files[i]["mtime"] - olean_files[i-1]["mtime"]
    module = olean_files[i]["module"]
    
    if module in native_decide_map:
        results.append({
            "module": module,
            "delta_t": delta_t,
            "native_decide_count": native_decide_map[module]
        })

# Sort by delta_t descending
results.sort(key=lambda x: x["delta_t"], reverse=True)

print(f"{'Module Name':<60} | {'Delta T (sec)':<15} | {'native_decide count':<20}")
print("-" * 100)
for r in results[:20]:
    print(f"{r['module']:<60} | {r['delta_t']:<15.2f} | {r['native_decide_count']:<20}")

