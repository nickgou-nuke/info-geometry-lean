import json
from pathlib import Path

from tools.pathing import default_docs_map_root, normalize_user_path

def load_declarations(manifest_path):
    with open(manifest_path) as f:
        manifest = json.load(f)
    # Example: expects manifest["core"] to be a list of declaration names
    return manifest.get("core", [])

def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", default=None, help="Path to manifest.json")
    ap.add_argument("--out", default=None, help="Output .tex file")
    args = ap.parse_args()

    docs_root = default_docs_map_root()
    manifest_path = normalize_user_path(args.manifest, docs_root / "manifest.json")
    out_path = normalize_user_path(args.out, Path("blueprint/src/generated/content.auto.tex"))
    decls = load_declarations(manifest_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w") as f:
        f.write("% AUTO-GENERATED FILE. DO NOT EDIT.\n")
        f.write("\\section*{Chapter 1. Core Foundations}\n\n")
        f.write("\\subsection*{Basic lemmas}\n\n")
        for decl in decls:
            f.write(f"\\inputleannode{{{decl}}}\n\n")

if __name__ == "__main__":
    main()
