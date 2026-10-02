import re

def get_decls(file_path):
    with open(file_path) as f:
        content = f.read()
    
    # We want def, theorem, lemma, structure, inductive
    # Lean 4 declaration regex
    pattern = r'^(?:(?:noncomputable|scoped|private|protected|unsafe)\s+)*(?:def|theorem|lemma|structure|inductive|class)\s+([A-Za-z0-9_.\']+)'
    
    # Also track namespaces
    lines = content.splitlines()
    ns_stack = []
    decls = []
    
    for line in lines:
        line_clean = line.split("--")[0].strip()
        m_ns = re.match(r'^namespace\s+([A-Za-z0-9_.]+)', line_clean)
        if m_ns:
            ns_stack.append(m_ns.group(1))
            continue
        m_end = re.match(r'^end(?:\s+([A-Za-z0-9_.]+))?', line_clean)
        if m_end:
            if ns_stack:
                ns_stack.pop()
            continue
        m_decl = re.match(pattern, line_clean)
        if m_decl:
            name = m_decl.group(1)
            full_name = ".".join(ns_stack + [name]) if ns_stack else name
            decls.append(full_name)
            
    return decls

for p in [
    "lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean",
    "lean/InfoGeometry/LLM/KreinAttentionEnergy.lean",
    "lean/DAG/ConnesHodgeBridge.lean"
]:
    print(f"=== {p} ===")
    for d in get_decls(p):
        print(f"  {d}")
