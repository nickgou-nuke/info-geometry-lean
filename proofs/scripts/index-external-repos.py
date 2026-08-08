#!/usr/bin/env python3
"""
Index external repositories into knowledge_base.json for RAG retrieval.

Scans the external/ directory for .lean and .py files and adds their
contents to the knowledge base for query_graph_rag.

Usage:
  source .venv/bin/activate
  python3 scripts/index-external-repos.py [--repo lean/atlas-lean] [--limit 100]

Without options, indexes all repositories with sensible limits per repo.
"""

import argparse
import json
import os
import re
import sys
from typing import Any, Dict, List

REPO_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)), "external")
KB_FILE = os.path.join(os.path.dirname(os.path.dirname(__file__)), "knowledge_base.json")

# Default limits per repo type
REPO_LIMITS = {
    "lean/atlas-lean": {"files": 200, "max_lines": 100, "extensions": [".lean"]},
    "lean/repoprover": {"files": 50, "max_lines": 200, "extensions": [".lean", ".py", ".md"]},
    "lean/lean-auto": {"files": 50, "max_lines": 200, "extensions": [".lean", ".md"]},
    "lean/atlas-embeddings": {"files": 30, "max_lines": 200, "extensions": [".py", ".json", ".md"]},
    "lean/VirasoroProject": {"files": 50, "max_lines": 200, "extensions": [".lean", ".md"]},
    "python/sympy": {"files": 100, "max_lines": 100, "extensions": [".py", ".md"]},
    "python/PauLie": {"files": 30, "max_lines": 200, "extensions": [".py", ".md"]},
    "python/SymPy-LieAlgebras": {"files": 30, "max_lines": 200, "extensions": [".py", ".md"]},
    "python/get-physics-done": {"files": 50, "max_lines": 200, "extensions": [".py", ".md"]},
    "math/affine-charform": {"files": 30, "max_lines": 200, "extensions": [".py", ".sage", ".md"]},
    "math/Semisimple-Lie-Algebras": {"files": 50, "max_lines": 200, "extensions": [".py", ".sage", ".md"]},
    "math/geoalg": {"files": 30, "max_lines": 200, "extensions": [".py", ".md"]},
    "math/SplitOct": {"files": 20, "max_lines": 200, "extensions": [".py", ".md"]},
    "math/RIA_EISA": {"files": 50, "max_lines": 100, "extensions": [".py", ".md"]},
    "python/quantum/QuAIRKit": {"files": 50, "max_lines": 200, "extensions": [".py", ".md"]},
    "python/quantum/qutip": {"files": 50, "max_lines": 200, "extensions": [".py", ".md"]},
    "python/pyw": {"files": 20, "max_lines": 200, "extensions": [".py", ".md"]},
    "python/sage": {"files": 100, "max_lines": 100, "extensions": [".py", ".md"]},
    "formal/isabelle/afp-devel": {"files": 100, "max_lines": 100, "extensions": [".thy", ".md"]},
}


def load_knowledge_base() -> List[Dict[str, Any]]:
    if os.path.exists(KB_FILE):
        with open(KB_FILE, "r") as f:
            data = json.load(f)
            if isinstance(data, list):
                return data
    return []


def save_knowledge_base(kb: List[Dict[str, Any]]):
    with open(KB_FILE, "w") as f:
        json.dump(kb, f, indent=2)
    print(f"💾 Saved {len(kb)} entries to {KB_FILE}")


def extract_lean_metadata(filepath: str, content: str) -> Dict[str, Any]:
    """Extract theorem names, imports, and structure from Lean files."""
    metadata = {
        "theorems": re.findall(r"(?:theorem|lemma|def)\s+([a-zA-Z0-9_']+)", content),
        "imports": re.findall(r"^\s*import\s+([a-zA-Z0-9_.]+)", content, re.MULTILINE),
    }
    return metadata


def index_repo(repo_path: str, config: Dict[str, Any], kb: List[Dict[str, Any]],
               existing_keys: set) -> int:
    """Index files from a repository into the knowledge base."""
    full_path = os.path.join(REPO_DIR, repo_path)
    if not os.path.exists(full_path):
        print(f"⚠️  {repo_path}: path not found, skipping")
        return 0

    count = 0
    extensions = config.get("extensions", [".lean"])
    max_files = config.get("files", 100)
    max_lines = config.get("max_lines", 100)

    for root, dirs, files in os.walk(full_path):
        # Skip hidden dirs and .git
        dirs[:] = [d for d in dirs if not d.startswith(".") and d != ".git"]

        for file in files:
            if count >= max_files:
                break
            if not any(file.endswith(ext) for ext in extensions):
                continue

            filepath = os.path.join(root, file)
            rel_path = os.path.relpath(filepath, REPO_DIR)

            # Create a unique key
            safe_key = re.sub(r'[^a-zA-Z0-9_]', '_', rel_path)
            if safe_key in existing_keys:
                continue

            try:
                with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
                    content = f.read()
            except Exception:
                continue

            if not content.strip():
                continue

            # Truncate long files
            lines = content.split("\n")
            if len(lines) > max_lines:
                content = "\n".join(lines[:max_lines]) + f"\n\n... [truncated at {max_lines} lines]"

            title = os.path.splitext(file)[0]
            metadata = extract_lean_metadata(filepath, content) if file.endswith(".lean") else {}

            entry = {
                "_key": safe_key[:200],  # ArangoDB key limit
                "title": f"{repo_path}/{title}",
                "content": content[:5000],  # Max 5KB per entry
                "source": f"external/{repo_path}",
                "tags": [repo_path.split("/")[0], os.path.splitext(file)[1].lstrip(".")],
                "status": "literature",
            }

            if metadata.get("theorems"):
                entry["theorems"] = metadata["theorems"][:50]
            if metadata.get("imports"):
                entry["imports"] = metadata["imports"][:20]

            kb.append(entry)
            existing_keys.add(safe_key)
            count += 1

    return count


def main():
    parser = argparse.ArgumentParser(description="Index external repos into knowledge base")
    parser.add_argument("--repo", help="Specific repo to index (e.g., lean/atlas-lean)")
    parser.add_argument("--limit", type=int, default=0,
                        help="Override file limit per repo")
    args = parser.parse_args()

    kb = load_knowledge_base()
    existing_keys = {entry.get("_key", "") for entry in kb}

    print(f"📚 Loaded {len(kb)} existing entries")
    print(f"🔍 Scanning external/ repositories...\n")

    total = 0

    if args.repo:
        repos = {args.repo: REPO_LIMITS.get(args.repo, {"files": 100, "extensions": [".lean", ".py", ".md"]})}
    else:
        repos = REPO_LIMITS

    for repo_name, config in repos.items():
        if args.limit > 0:
            config = {**config, "files": args.limit}
        count = index_repo(repo_name, config, kb, existing_keys)
        if count > 0:
            print(f"  📄 {repo_name}: indexed {count} files")
        total += count

    print(f"\n✅ Indexed {total} new entries (total: {len(kb)})")
    save_knowledge_base(kb)


if __name__ == "__main__":
    main()
