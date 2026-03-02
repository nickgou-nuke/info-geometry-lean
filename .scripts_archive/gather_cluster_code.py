#!/usr/bin/env python3
import json
import sys
from pathlib import Path

# Add project root to path for tools
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tools.graph import ProjectGraph

def main():
    if len(sys.argv) < 2:
        print("Usage: gather_cluster_code.py <cluster_index>")
        return

    cluster_idx = int(sys.argv[1])
    
    with open("theory_manifest.json", "r") as f:
        manifest = json.load(f)

    clusters = manifest["clusters"]
    if str(cluster_idx) not in clusters:
        print(f"Error: Cluster {cluster_idx} not found in manifest.")
        return

    cluster = clusters[str(cluster_idx)]
    members = cluster["nodes"]
    hub = cluster["hub"]

    print(f"--- Cluster {cluster_idx}: {hub} (Full Context) ---")
    
    pg = ProjectGraph()
    files_to_harvest = set()

    for member in members:
        path = pg.get_file_path(member)
        if path:
            files_to_harvest.add(path)

    context = []
    for path in sorted(files_to_harvest):
        content = path.read_text(encoding="utf-8")
        context.append(f"== FILE: {path} ==\n{content}\n")

    output_path = Path(f"cluster_{cluster_idx}_full_context.txt")
    output_path.write_text("\n".join(context))
    print(f"Gathered {len(files_to_harvest)} full files into {output_path}")

if __name__ == "__main__":
    main()
