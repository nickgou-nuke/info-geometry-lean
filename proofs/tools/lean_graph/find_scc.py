#!/usr/bin/env python3
"""
Find Strongly Connected Components (SCCs) in the Lean proof graph.
Enforces that the theory topology is a pure DAG with no cyclic dependencies.
"""

import json
import sys
from pathlib import Path

def tarjan(graph):
    index = 0
    stack = []
    indices = {}
    lowlinks = {}
    on_stack = set()
    sccs = []

    def strongconnect(v):
        nonlocal index
        indices[v] = index
        lowlinks[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)

        for w in graph.get(v, []):
            if w not in indices:
                strongconnect(w)
                lowlinks[v] = min(lowlinks[v], lowlinks[w])
            elif w in on_stack:
                lowlinks[v] = min(lowlinks[v], indices[w])

        if lowlinks[v] == indices[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                scc.append(w)
                if w == v:
                    break
            sccs.append(scc)

    for v in graph:
        if v not in indices:
            strongconnect(v)

    return sccs

def main():
    if len(sys.argv) > 1:
        json_path = Path(sys.argv[1])
    else:
        json_path = Path("proof_graph.json")
    
    if not json_path.exists():
        print(f"Error: {json_path} not found.")
        sys.exit(1)
        
    with open(json_path, "r", encoding="utf-8") as f:
        records = json.load(f)
        
    # Build graph
    graph = {}
    for r in records:
        name = r.get("name")
        deps = r.get("deps", [])
        if name:
            graph[name] = deps
            
    # Include nodes that only appear in dependencies
    for r in records:
        for d in r.get("deps", []):
            if d not in graph:
                graph[d] = []

    sccs = tarjan(graph)
    
    non_trivial = [scc for scc in sccs if len(scc) > 1]
    
    if non_trivial:
        print(f"FAILED: Found {len(non_trivial)} non-trivial SCCs (cyclic dependencies)!")
        for i, scc in enumerate(non_trivial):
            print(f"SCC {i+1}: {scc}")
        sys.exit(1)
    else:
        print(f"SUCCESS: Graph is a valid DAG. 0 non-trivial SCCs found across {len(graph)} nodes.")

if __name__ == "__main__":
    main()
