#!/usr/bin/env python3
"""
Push gap catalog to ArangoDB Hive Memory.
"""

import json
from datetime import datetime, timezone
from arango import ArangoClient

ARANGO_HOST = "http://localhost:8530"
ARANGO_USER = "root"
ARANGO_PASS = "alexandria_root"
DB_NAME = "hive_memory"

def main():
    # Load catalog
    with open('artifacts/gap_catalog.json') as f:
        catalog = json.load(f)
    
    client = ArangoClient(hosts='http://localhost:8530')
    db = client.db('hive_memory', username='root', password='alexandria_root')
    
    thoughts = db.collection('Thoughts')
    
    # Clear existing data
    thoughts.truncate()
    
    # Insert catalog as a thought
    catalog_key = f"gap_catalog_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}"
    catalog_doc = {
        '_key': f"gap_catalog_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}",
        'type': 'gap_catalog',
        'payload': json.load(open('artifacts/gap_catalog.json')),
        'created_at': datetime.now(timezone.utc).isoformat() + 'Z'
    }
    db.collection('Thoughts').insert(catalog_doc)
    print(f"Inserted catalog")
    
    # Insert individual gaps
    with open('artifacts/axiom_audit_report.json') as f:
        axiom = json.load(f)
    
    for f in axiom.get('files', []):
        if f.get('total_gaps', 0) > 0:
            thought = {
                '_key': f"gap_{f['file'].replace('/', '_').replace('.lean', '').replace('.', '_')}",
                'type': 'axiom_gap',
                'file': f['file'],
                'total_gaps': f['total_gaps'],
                'sorry_count': len(f.get('sorry_lines', [])),
                'axiom_count': len(f.get('axiom_lines', [])),
                'admit_count': len(f.get('admit_lines', [])),
                'details': {
                    'sorry_lines': f.get('sorry_lines', []),
                    'axiom_lines': f.get('axiom_lines', []),
                    'admit_lines': f.get('admit_lines', [])
                },
                'created_at': datetime.now(timezone.utc).isoformat() + 'Z'
            }
            try:
                db.collection('Thoughts').insert(thought)
            except Exception as e:
                print(f"Warning: Failed to insert {f['file']}: {e}")
    
    print("Successfully pushed to ArangoDB Hive Memory")

if __name__ == '__main__':
    import json
    from datetime import datetime, timezone
    from arango import ArangoClient
    
    main()
EOF