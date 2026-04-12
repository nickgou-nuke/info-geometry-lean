#!/usr/bin/env python3
import os
import re
import json
import sys
from pathlib import Path

"""
# Trace and Retrieve (Spire Edition)
Lightweight repository indexing and premise retrieval engine.
Usage: python3 trace_and_retrieve.py --query "Drazin" --top-k 5
"""

def index_repository(root_path):
    """Simple regex-based indexer for Lean 4 theorems and definitions."""
    index = []
    lean_files = list(Path(root_path).rglob("*.lean"))
    
    # Matches: theorem/def name ... : type
    # Includes optional docstrings
    pattern = re.compile(r"(?:/--\s*(.*?)\s*-/)?\s*(?:@[^\]]*\]\s*)?(?:theorem|lemma|def|structure|inductive)\s+([\w\.]+)", re.DOTALL)

    for file_path in lean_files:
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
    return index

def retrieve(index, query, top_k=5):
    """Simple keyword-based relevance matching."""
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
    
    # Sort by score and return top_k
    results.sort(key=lambda x: x[0], reverse=True)
    return [res[1] for res in results[:top_k]]

def main():
    root_path = Path("./")
    
    if "--query" in sys.argv:
        query_idx = sys.argv.index("--query") + 1
        query = sys.argv[query_idx]
        
        top_k = 5
        if "--top-k" in sys.argv:
            k_idx = sys.argv.index("--top-k") + 1
            top_k = int(sys.argv[k_idx])
            
        index = index_repository(root_path)
        results = retrieve(index, query, top_k)
        
        if results:
            print(f"--- [RETRIEVAL] Results for '{query}' ---")
            for res in results:
                print(f"[{res['file']}] {res['name']}")
                if res['docstring']:
                    print(f"  Doc: {res['docstring'][:100]}...")
                print("-" * 20)
        else:
            print(f"No results found for '{query}'.")
    else:
        print("Usage: python3 trace_and_retrieve.py --query <keyword> [--top-k <n>]")

if __name__ == "__main__":
    main()
