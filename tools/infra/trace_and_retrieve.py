#!/usr/bin/env python3
import os
import re
import json
import sys
import subprocess
from pathlib import Path

"""
# Hardened Spire Trace (Two-Phase)
Phase 1: Offline Build (--build-index) -> Creates git-SHA indexed cache.
Phase 2: Online Retrieval (--query)   -> Loads cache for task-local query.
"""

def get_git_sha():
    try:
        return subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode('ascii').strip()
    except:
        return "unknown_sha"

def get_cache_path(sha):
    cache_dir = Path(".spire_cache")
    cache_dir.mkdir(exist_ok=True)
    return cache_dir / f"trace_index_{sha}.json"

def build_index(root_path):
    """Deep scan of the repository for formal declarations and docstrings."""
    print(f"--- [BUILD] Indexing repository at {root_path} ---")
    index = []
    lean_files = list(Path(root_path).rglob("*.lean"))
    
    # Matches: theorem/def name ... : type
    pattern = re.compile(r"(?:/--\s*(.*?)\s*-/)?\s*(?:@[^\]]*\]\s*)?(?:theorem|lemma|def|structure|inductive)\s+([\w\.]+)", re.DOTALL)

    for file_path in lean_files:
        try:
            with open(file_path, "r") as f:
                content = f.read()
                for match in pattern.finditer(content):
                    docstring = match.group(1).strip() if match.group(1) else ""
                    name = match.group(2)
                    index.append({
                        "name": name,
                        "docstring": docstring,
                        "file": str(file_path.relative_to(root_path))
                    })
        except Exception as e:
            print(f"Warning: Could not index {file_path}: {e}")
            
    sha = get_git_sha()
    cache_file = get_cache_path(sha)
    with open(cache_file, "w") as f:
        json.dump(index, f, indent=2)
    print(f"SUCCESS: Index built for commit {sha[:8]} at {cache_file}")
    return cache_file

def retrieve(cache_file, query, top_k=5):
    """Fast retrieve from cached JSON."""
    if not cache_file.exists():
        print(f"Error: Cache index {cache_file} not found. Run --build-index first.")
        sys.exit(1)
        
    with open(cache_file, "r") as f:
        index = json.load(f)
        
    query = query.lower()
    results = []
    for item in index:
        score = 0
        if query in item["name"].lower():
            score += 10
        if query in item["docstring"].lower():
            score += 5
        
        if score > 0:
            results.append((score, item))
    
    results.sort(key=lambda x: x[0], reverse=True)
    return [res[1] for res in results[:top_k]]

def main():
    if "--build-index" in sys.argv:
        build_index(Path("./"))
    elif "--query" in sys.argv:
        query_idx = sys.argv.index("--query") + 1
        query = sys.argv[query_idx]
        
        sha = get_git_sha()
        cache_file = get_cache_path(sha)
        
        results = retrieve(cache_file, query)
        if results:
            print(f"--- [RETRIEVAL] Results for '{query}' ---")
            for res in results:
                print(f"[{res['file']}] {res['name']}")
                if res['docstring']:
                    print(f"  Doc: {res['docstring'][:100]}...")
        else:
            print(f"No results found for '{query}'.")
    else:
        print("Usage: python3 trace_and_retrieve.py [--build-index | --query <keyword>]")

if __name__ == "__main__":
    main()
