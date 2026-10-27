#!/usr/bin/env python3
"""Extract a dependency partial order from checked Lean declaration JSONL.

This is a record of the chosen proofs' constant dependencies, not a claim of
unique mathematical necessity, a topology, or a homotopy of concepts.
"""
import hashlib
import json
from pathlib import Path
import sys

if len(sys.argv) != 3:
    raise SystemExit("usage: operator_geometry_dependency_order.py AUDIT_JSONL OUTPUT_JSON")
log, output = map(Path, sys.argv[1:])
records = []
summaries = []
for line in log.read_text().splitlines():
    if not line.startswith("{"):
        continue
    record = json.loads(line)
    if record.get("record") == "declaration":
        records.append(record)
    elif record.get("record") == "summary":
        summaries.append(record)
if not summaries or summaries[-1].get("status") != "PASS":
    raise SystemExit("No passing kernel declaration audit")
by_name = {record["name"]: record for record in records}
if len(by_name) != len(records) or len(records) != summaries[-1]["declarations"]:
    raise SystemExit("Duplicate or missing declarations")
deps = {name: set(record["owned_dependencies"]) for name, record in by_name.items()}
for name, incoming in deps.items():
    if not incoming <= by_name.keys() or name in incoming:
        raise SystemExit("Unresolved or recursive owned dependency: " + name)
remaining = {name: incoming.copy() for name, incoming in deps.items()}
layers = []
order = []
while remaining:
    layer = sorted(name for name, incoming in remaining.items() if not incoming)
    if not layer:
        raise SystemExit("A dependency cycle prevents a partial order")
    layers.append(layer)
    order.extend(layer)
    for name in layer:
        del remaining[name]
    for incoming in remaining.values():
        incoming.difference_update(layer)
ancestors = {}
for name in order:
    ancestors[name] = deps[name].copy()
    for parent in deps[name]:
        ancestors[name].update(ancestors[parent])
edges = sorted((parent, name) for name, incoming in deps.items() for parent in incoming)
covers = sorted((parent, name) for name, incoming in deps.items() for parent in incoming
                if not any(parent in ancestors[other] for other in incoming - {parent}))
result = {
    "scope": "Constants in checked declaration types and values, restricted to four new owners",
    "relation": "a <= b iff a = b or b transitively depends on a",
    "orientation": "dependency -> dependent",
    "is_dag": True,
    "audit_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
    "declaration_count": len(records),
    "theorem_count": sum(record["kind"] == "theorem" for record in records),
    "nodes": records, "direct_edges": edges, "hasse_edges": covers,
    "topological_order": order, "layers": layers,
    "axioms": sorted({ax for record in records for ax in record["axioms"]}),
}
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({key: result[key] for key in
                  ("is_dag", "declaration_count", "theorem_count", "axioms")}))
