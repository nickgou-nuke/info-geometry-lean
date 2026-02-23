import json
from pathlib import Path

from tools.pathing import lean_root, normalize_user_path

def extract_blueprint_nodes():
    # Scan Lean module header for \newleannode definitions
    # resolve relative to lean root
    header_path = lean_root() / ".lake/build/blueprint/module/InfoGeometry/Core.tex"
    nodes = []
    with header_path.open() as f:
        for line in f:
            if line.strip().startswith("\\newleannode{"):
                name = line.split('{')[1].split('}')[0]
                nodes.append(name)
    return nodes

def main():
    out_path = normalize_user_path(None, Path("blueprint/src/generated/content.auto.tex"))
    out_path.parent.mkdir(parents=True, exist_ok=True)
    nodes = extract_blueprint_nodes()
    with out_path.open("w") as f:
        f.write("% AUTO-GENERATED FILE. DO NOT EDIT.\n")
        f.write("\\section*{Chapter 1. Core Foundations}\n\n")
        f.write("\\subsection*{Basic lemmas}\n\n")
        for node in nodes:
            f.write(f"\\inputleannode{{{node}}}\n\n")

if __name__ == "__main__":
    main()
