import os
import glob
import re
import hashlib
from arango import ArangoClient

client = ArangoClient(hosts='http://localhost:8529')
db = client.db('agent_brain', username='root', password='')
nodes = db.collection('lean_theorems')

proofs_dir = '/home/goutev/auto/proofs/'
pattern = os.path.join(proofs_dir, '*.lean')

# Regexes to find generalized sorrys: True := trivial, def X := 0, or := by rfl
regex_trivial = re.compile(r'theorem\s+([a-zA-Z0-9_]+)\s*.*:\s*True\s*:=\s*trivial')
regex_def0 = re.compile(r'def\s+([a-zA-Z0-9_]+)[^=]*?:\s*(?:Prop|ℕ|ℤ|ℚ|ℝ|ℂ|Q)\s*:=\s*0')

found_nodes = []

for filepath in glob.glob(pattern):
    filename = os.path.basename(filepath)
    with open(filepath, 'r') as f:
        content = f.read()
        
        for match in regex_trivial.finditer(content):
            name = match.group(1)
            ast_content = match.group(0).strip()
            db_hash = hashlib.sha256(ast_content.encode('utf-8')).hexdigest()
            found_nodes.append({
                "_key": name,
                "type": "Cohomological_Boundary_Zero",
                "file": filename,
                "status": "Generalized_Sorry",
                "equation": "True := trivial",
                "de_bruijn_hash": db_hash,
                "ast_content": ast_content
            })
            
        for match in regex_def0.finditer(content):
            name = match.group(1)
            ast_content = match.group(0).strip()
            db_hash = hashlib.sha256(ast_content.encode('utf-8')).hexdigest()
            found_nodes.append({
                "_key": name,
                "type": "Cohomological_Boundary_Zero",
                "file": filename,
                "status": "Generalized_Sorry",
                "equation": "def X := 0",
                "de_bruijn_hash": db_hash,
                "ast_content": ast_content
            })

inserted = 0
updated = 0
for node in found_nodes:
    if not nodes.has(node['_key']):
        nodes.insert(node)
        inserted += 1
    else:
        nodes.update(node)
        updated += 1

print(f"Updated compiled theory graph: {inserted} inserted, {updated} updated with generalized sorry hashes.")
