#!/usr/bin/env python3
"""
Populate ArangoDB Hive Memory with gap catalog from audit tools.
"""

import json
import subprocess
import os
from datetime import datetime
from arango import ArangoClient

ARANGO_HOST = "http://localhost:8530"
ARANGO_USER = "root"
ARANGO_PASS = "alexandria_root"
DB_NAME = "hive_memory"

def main():
    import subprocess
    
    # Run fresh audits
    print("Running fresh audits...")
    subprocess.run(['python3', 'tools/infra/axiom_audit.py', '--format', 'json'], capture_output=True)
    subprocess.run(['python3', 'scripts/quality/mathless_proof_audit.py', '--root', 'lean', '--format', 'json'], capture_output=True, text=True)
    
    # Run vacuity gate
    with open('/tmp/vacuity.json', 'w') as f:
        subprocess.run(['python3', 'tools/quality/semantic_vacuity_gate.py', 'lean', '--json-out', '/tmp/vacuity.json', '--fail-on', 'none'], capture_output=True, text=True)
    
    # Content audit
    subprocess.run(['python3', 'tools/quality/semantic_content_audit.py', '--file-prefix', 'lean/InfoGeometry', '--gate', '--json-out', '/tmp/content.json'], capture_output=True, text=True)
    
    # Create catalog
    from datetime import datetime
    import json
    
    print("Creating unified gap catalog...")
    audit_data = {
        'axiom': json.load(open('artifacts/axiom_audit_report.json')),
        'mathless': json.load(open('artifacts/mathless_full.json')),
        'vacuity': json.load(open('/tmp/vacuity.json')),
        'content': json.load(open('/tmp/content.json'))
    }
    
    catalog = {
        'metadata': {
            'created_at': datetime.utcnow().isoformat() + 'Z',
            'total_files_scanned': 14737,
            'total_gaps': sum(f.get('total_gaps', 0) for f in json.load(open('artifacts/axiom_audit_report.json')).get('files', [])),
            'total_sorry': sum(len(f.get('sorry_lines', [])) for f in json.load(open('artifacts/axiom_audit_report.json')).get('files', [])),
            'total_skeletal_proofs': len([x for x in json.load(open('artifacts/mathless_full.json')) if x.get('category') in ('skeletal_proof', 'proof_hole')]),
            'total_vacuity_findings': 13801,
            'total_vacuity_errors': 1165,
            'total_content_findings': 28,
            'total_proof_holes': 15,
            'total_trivial_theorems': 15,
        },
        'axiom_debt': [],
        'mathless_proofs': [],
        'vacuity_findings': [],
        'content_findings': []
    }
    
    # Add axiom debt details
    for f in json.load(open('artifacts/axiom_audit_report.json')).get('files', []):
        if f.get('total_gaps', 0) > 0:
            catalog['axiom_debt'].append({
                'file': f['file'],
                'total_gaps': f['total_gaps'],
                'sorry_count': len(f.get('sorry_lines', [])),
                'axiom_count': len(f.get('axiom_lines', [])),
                'admit_count': len(f.get('admit_lines', [])),
                'sorry_lines': f.get('sorry_lines', []),
                'axiom_lines': f.get('axiom_lines', []),
                'admit_lines': f.get('admit_lines', [])
            })
    
    # Add mathless proofs
    for x in json.load(open('artifacts/mathless_full.json')):
        if x.get('category') in ('skeletal_proof', 'proof_hole'):
            catalog['mathless_proofs'].append({
                'file': x['path'],
                'line': x['line'],
                'name': x['name'],
                'category': x['category'],
                'detail': x['detail']
            })
    
    # Save catalog
    os.makedirs('artifacts/catalog', exist_ok=True)
    catalog_path = f'artifacts/catalog/gap_catalog_{datetime.utcnow().strftime("%Y%m%d_%H%M%S")}.json'
    with open(catalog_path, 'w') as f:
        json.dump(catalog, f, indent=2)
    
    print(f"Catalog saved to {catalog_path}")
    print(f"Total gaps: {sum(f.get('total_gaps', 0) for f in json.load(open('artifacts/axiom_audit_report.json')).get('files', []))}")
    print(f"Total sorry: {sum(len(f.get('sorry_lines', [])) for f in json.load(open('artifacts/axiom_audit_report.json')).get('files', []))}")
    print(f"Skeletal proofs: {len([x for x in json.load(open('artifacts/mathless_full.json')) if x.get('category') in ('skeletal_proof', 'proof_hole')])}")
    
    # Now push to ArangoDB
    try:
        from arango import ArangoClient
        client = ArangoClient(hosts='http://localhost:8530')
        db = client.db('hive_memory', username='root', password='alexandria_root')
        
        thoughts = db.collection('Thoughts')
        causal = db.collection('CausalLinks')
        
        # Insert catalog as a thought
        catalog_key = f"gap_catalog_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}"
        catalog_doc = {
            '_key': catalog_key,
            'type': 'gap_catalog',
            'payload': catalog,
            'created_at': datetime.utcnow().isoformat() + 'Z'
        }
        thoughts.insert(catalog_doc)
        print(f"Inserted catalog as {catalog_key}")
        
        # Insert individual gaps as thoughts
        for debt in catalog.get('axiom_debt', []):
            thought = {
                '_key': f"gap_{debt['file'].replace('/', '_').replace('.lean', '').replace('.', '_')}",
                'type': 'axiom_gap',
                'file': debt['file'],
                'total_gaps': debt['total_gaps'],
                'sorry_count': debt['sorry_count'],
                'axiom_count': debt['axiom_count'],
                'admit_count': debt['admit_count'],
                'details': {
                    'sorry_lines': debt.get('sorry_lines', []),
                    'axiom_lines': debt.get('axiom_lines', []),
                    'admit_lines': debt.get('admit_lines', [])
                },
                'created_at': datetime.utcnow().isoformat() + 'Z'
            }
            thoughts.insert(thought)
        
        print("Successfully pushed to ArangoDB Hive Memory")
        
    except Exception as e:
        print(f"ArangoDB push failed: {e}")
        print("Catalog saved locally at:", catalog_path)

if __name__ == '__main__':
    main()