#!/usr/bin/env python3
"""Export the active mathematical spine as a Graphviz DOT file."""
from arango import ArangoClient

db = ArangoClient(hosts="http://localhost:8529").db("info_geometry", username="root", password="")

# Key spine nodes by module
SPINE_MODULES = [
    "SplitClifford", "ChiralCausalCone", "ChiralTensorRecoupling",
    "TLChain", "JonesBraidB3", "B3PresentedGroup",
    "YangBaxterQSwap", "YangBaxterQuotientDescent",
    "ChiralTLDescent", "BraidIdealDescent", "ChiralTensorMatrixBridge",
    "ChiralB3PresentedBridge", "SupergradedCuntzBdG"
]

# Collect all spine nodes and their inter-module references
edges = []
nodes = set()
modules_seen = set()
theorems_seen = set()

for mod in SPINE_MODULES:
    cursor = db.aql.execute("""
        FOR a IN lean_decls FILTER a.module == @mod AND a.kind == "theorem"
          FOR v, e IN 1..3 OUTBOUND a._id references
            FILTER v.module IN @spine AND v.module != @mod
            SORT a.name, v.name
            LIMIT 5
            RETURN {from: a.name, to: v.name, from_mod: a.module, to_mod: v.module}
    """, bind_vars={"mod": mod, "spine": SPINE_MODULES})
    for r in cursor:
        edges.append(r)
        nodes.add(r['from'])
        nodes.add(r['to'])
        modules_seen.add(r['from_mod'])
        modules_seen.add(r['to_mod'])
        if r['from_mod'] != r['to_mod']:
            theorems_seen.add(r['from'])

# Generate DOT
dot = ['digraph GEPA_Active_Spine {',
       '  rankdir=LR;',
       '  node [shape=box, style=filled, fillcolor=lightyellow];',
       '  edge [fontsize=9];',
       '']

# Module clusters
for mod in sorted(SPINE_MODULES):
    if mod in modules_seen:
        dot.append(f'  subgraph cluster_{mod} {{')
        dot.append(f'    label="{mod}";')
        dot.append(f'    color=lightblue;')
        for n in sorted(nodes):
            if n.startswith(mod):
                short = n.replace(mod + ".", "")
                dot.append(f'    "{n}" [label="{short}", shape=ellipse, fillcolor=lightgreen];')
        dot.append('  }')

# Inter-module edges (one per module pair, labeled with count)
dot.append('')
from collections import Counter
edge_counts = Counter()
for e in edges:
    if e['from_mod'] != e['to_mod']:
        edge_counts[(e['from_mod'], e['to_mod'])] += 1

for (frm, to), cnt in sorted(edge_counts.items()):
    dot.append(f'  "{frm}" -> "{to}" [label="{cnt} thms", color=blue];')

dot.append('}')
dot_text = '\n'.join(dot)

path = "tools/lean_graph/out/active_spine.dot"
with open(path, "w") as f:
    f.write(dot_text)
print(f"DOT: {path}")
print(f"  Modules: {len(modules_seen)}")
print(f"  Theorems: {len(theorems_seen)}")
print(f"  Cross-module edges: {len(edge_counts)}")
