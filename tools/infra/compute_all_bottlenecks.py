import os

# Get all olean files and their modification times
olean_files = []
for root, dirs, files in os.walk(".lake/build/lib/lean"):
    for file in files:
        if file.endswith(".olean"):
            full_path = os.path.join(root, file)
            mtime = os.path.getmtime(full_path)
            
            # Extract module name from path
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
    results.append({
        "module": module,
        "delta_t": delta_t
    })

# Sort by delta_t descending
results.sort(key=lambda x: x["delta_t"], reverse=True)

print(f"{'Module Name':<70} | {'Delta T (sec)':<15}")
print("-" * 88)
for r in results[:30]:
    print(f"{r['module']:<70} | {r['delta_t']:<15.2f}")

