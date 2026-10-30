"""Shared iterative graph-component algorithms for repository analysis."""
from __future__ import annotations

from typing import Iterable


def tarjan_scc(vertices: Iterable[str], adjacency: dict[str, list[str]]) -> list[list[str]]:
    """Return directed strongly connected components without recursion limits."""
    index_of: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    on_stack: set[str] = set()
    stack: list[str] = []
    components: list[list[str]] = []
    counter = 0

    for root in vertices:
        if root in index_of:
            continue
        index_of[root] = lowlink[root] = counter
        counter += 1
        stack.append(root)
        on_stack.add(root)
        call_stack: list[tuple[str, list[str], int]] = [(root, adjacency.get(root, []), 0)]
        while call_stack:
            node, neighbors, pos = call_stack.pop()
            descended = False
            i = pos
            while i < len(neighbors):
                nxt = neighbors[i]
                i += 1
                if nxt not in index_of:
                    call_stack.append((node, neighbors, i))
                    index_of[nxt] = lowlink[nxt] = counter
                    counter += 1
                    stack.append(nxt)
                    on_stack.add(nxt)
                    call_stack.append((nxt, adjacency.get(nxt, []), 0))
                    descended = True
                    break
                if nxt in on_stack and index_of[nxt] < lowlink[node]:
                    lowlink[node] = index_of[nxt]
            if descended:
                continue
            if call_stack:
                parent = call_stack[-1][0]
                lowlink[parent] = min(lowlink[parent], lowlink[node])
            if lowlink[node] == index_of[node]:
                component: list[str] = []
                while True:
                    member = stack.pop()
                    on_stack.discard(member)
                    component.append(member)
                    if member == node:
                        break
                components.append(sorted(component))
    return sorted(components, key=lambda component: component[0] if component else "")
