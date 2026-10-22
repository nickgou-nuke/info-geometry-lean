import os
import re
import sys
from pathlib import Path
from arango import ArangoClient

# Configure python path
sys.path.insert(0, os.path.abspath('.'))
sys.path.insert(0, os.path.abspath('./src'))

from tools.infra.arango_env import (
    load_repo_arango_env,
    arango_endpoint,
    arango_username,
    arango_password,
    arango_database,
)

def get_module_name(filepath):
    # e.g., lean/InfoGeometry/Lie/Pin55KreinConformalBridge.lean -> InfoGeometry.Lie.Pin55KreinConformalBridge
    rel = os.path.relpath(filepath, "lean")
    base, _ = os.path.splitext(rel)
    return base.replace("/", ".")

def find_sorry_decls():
    lean_dir = "lean/InfoGeometry"
    decl_re = re.compile(r'^\s*(?:noncomputable\s+)?(?:protected\s+)?(?:private\s+)?(theorem|def|lemma|instance)\s+(\w+)')
    sorry_re = re.compile(r'\b(sorry|admit)\b')
    
    sorry_decls = []
    
    for root, _, files in os.walk(lean_dir):
        for file in files:
            if file.endswith(".lean"):
                filepath = os.path.join(root, file)
                module = get_module_name(filepath)
                
                with open(filepath, 'r') as f:
                    lines = f.readlines()
                
                current_decl = None
                decl_has_sorry = False
                
                for line in lines:
                    m = decl_re.match(line)
                    if m:
                        # We hit a new declaration. Save the old one if it had a sorry.
                        if current_decl and decl_has_sorry:
                            sorry_decls.append(f"{module}.{current_decl}")
                        current_decl = m.group(2)
                        decl_has_sorry = False
                    
                    if current_decl and sorry_re.search(line):
                        decl_has_sorry = True
                
                # Check the last declaration in the file
                if current_decl and decl_has_sorry:
                    sorry_decls.append(f"{module}.{current_decl}")
                    
    return sorry_decls

def main():
    load_repo_arango_env(Path('.').resolve())
    client = ArangoClient(hosts=arango_endpoint())
    db = client.db(arango_database(), username=arango_username(), password=arango_password())
    
    print("Scanning source files for sorry declarations...")
    sorry_decls = find_sorry_decls()
    print(f"Found {len(sorry_decls)} declarations with sorry in the source code.")
    
    report_lines = []
    report_lines.append("# Candidate value-fingerprint matches for source declarations containing sorry\n")
    report_lines.append("Matching finite hashes are navigation candidates only. They do not establish structural identity, theorem equivalence, or shared proof debt.\n\n")
    
    audited_hashes = set()
    
    for decl_name in sorry_decls:
        # Resolve the versioned value hash for this declaration.
        q = 'FOR d IN decls FILTER d.name == @name RETURN d'
        res = list(db.aql.execute(q, bind_vars={"name": decl_name}))
        if not res:
            continue
        
        doc = res[0]
        val_fp = doc.get("valueFingerprint")
        if not val_fp:
            continue
        
        if val_fp.get("algorithmVersion") != "lean-expr-structural-v3":
            continue
        shape_hash = doc.get("canonicalValueHash")
        if shape_hash is None or shape_hash in audited_hashes:
            continue
        
        audited_hashes.add(shape_hash)
        
        # Find every declaration sharing the same versioned candidate hash.
        q_equiv = '''
        FOR d IN decls
          FILTER d.valueFingerprint.algorithmVersion == "lean-expr-structural-v3"
          FILTER d.canonicalValueHash == @hash
          RETURN {name: d.name, module: d.module}
        '''
        matches = list(db.aql.execute(q_equiv, bind_vars={"hash": shape_hash}))
        
        report_lines.append(f"### Source declaration: `{decl_name}`\n")
        report_lines.append(f"- **Candidate value hash**: `{shape_hash}`\n")
        report_lines.append(f"- **Matching declarations**: {len(matches)}\n\n")
        report_lines.append("Declarations sharing this hash (inspect source individually):\n")
        for match in matches:
            report_lines.append(f"  - `{match['name']}` ({match['module']})\n")
        report_lines.append("\n---\n\n")
        
    report_path = Path("astaqlhash_sorry_equivalents_detailed.md")
    with open(report_path, "w") as out:
        out.writelines(report_lines)
        
    print(f"Detailed candidate-match report written to: {report_path}")

if __name__ == "__main__":
    main()
