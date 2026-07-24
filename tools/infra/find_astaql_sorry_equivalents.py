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
    report_lines.append("# Detailed sorry-equivalent structural audit report\n")
    report_lines.append("This report lists all declarations containing `sorry` in the source code, resolves their `valueFingerprint.shapeHash`, and identifies all other declarations in the codebase that share the same shape hash (sorry-equivalents).\n\n")
    
    audited_hashes = set()
    
    for decl_name in sorry_decls:
        # Query the shape hash for this declaration
        q = f'FOR d IN decls FILTER d.name == "{decl_name}" RETURN d'
        res = list(db.aql.execute(q))
        if not res:
            continue
        
        doc = res[0]
        val_fp = doc.get("valueFingerprint")
        if not val_fp:
            continue
        
        shape_hash = val_fp.get("shapeHash")
        if not shape_hash or shape_hash in audited_hashes:
            continue
        
        audited_hashes.add(shape_hash)
        
        # Query all other declarations sharing this value shape hash
        q_equiv = f'''
        FOR d IN decls
          FILTER d.valueFingerprint.shapeHash == "{shape_hash}"
          RETURN {{name: d.name, module: d.module}}
        '''
        equivalents = list(db.aql.execute(q_equiv))
        
        report_lines.append(f"### Source Sorry: `{decl_name}`\n")
        report_lines.append(f"- **Value Shape Hash**: `{shape_hash}`\n")
        report_lines.append(f"- **Total Equivalents**: {len(equivalents)}\n\n")
        report_lines.append("Sharing declarations:\n")
        for eq in equivalents:
            report_lines.append(f"  - `{eq['name']}` ({eq['module']})\n")
        report_lines.append("\n---\n\n")
        
    report_path = Path("astaqlhash_sorry_equivalents_detailed.md")
    with open(report_path, "w") as out:
        out.writelines(report_lines)
        
    print(f"Detailed sorry equivalence report written to: {report_path}")

if __name__ == "__main__":
    main()
