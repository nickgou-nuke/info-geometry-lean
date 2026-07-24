import sys
import os
import json
from pathlib import Path
from arango import ArangoClient
sys.path.insert(0, os.path.abspath('.'))
sys.path.insert(0, os.path.abspath('./src'))

from tools.infra.arango_env import (
    load_repo_arango_env,
    arango_endpoint,
    arango_username,
    arango_password,
    arango_database,
)

def main():
    # 1. Load environment
    load_repo_arango_env(Path('.').resolve())
    client = ArangoClient(hosts=arango_endpoint())
    db = client.db(arango_database(), username=arango_username(), password=arango_password())

    print("=== ASTAQLHASH Sorry-Equivalence Audit ===")

    # 2. Define the targeted AQL query
    # We group declarations by their valueFingerprint shapeHash and look for those that contain sorry, true, or trivial
    q = '''
    FOR d IN decls
      FILTER d.valueFingerprint != null
      LET name_lower = LOWER(d.name)
      FILTER name_lower LIKE "%sorry%"
          OR name_lower LIKE "%_true%"
          OR name_lower LIKE "%trivial%"
      COLLECT hash = d.valueFingerprint.shapeHash INTO members
      FILTER hash != null
      SORT LENGTH(members) DESC
      RETURN {
        valueShapeHash: hash,
        count: LENGTH(members),
        declarations: members[*].d.name
      }
    '''

    results = list(db.aql.execute(q))
    
    # 3. Write results to markdown artifact
    report_path = Path("astaqlhash_sorry_equivalents_report.md")
    with open(report_path, "w") as f:
        f.write("# ASTAQLHASH Sorry-Equivalence Audit Report\n\n")
        f.write("This report maps structural shape equivalence classes in ArangoDB matching `sorry`, `true`/`_True`, or `trivial` keywords, identifying their corresponding `valueShapeHash` signatures.\n\n")
        
        f.write("## Identified Sorry/Trivial/True ValueShapeHash Signatures\n\n")
        for row in results:
            hash_val = row["valueShapeHash"]
            count = row["count"]
            f.write(f"### Signature Hash: `{hash_val}` (Total: {count} declarations)\n")
            f.write("Classified as: **Open Debt Sorry-Equivalent**\n\n")
            f.write("Declarations in this equivalence class:\n")
            for decl in row["declarations"]:
                f.write(f"- `{decl}`\n")
            f.write("\n---\n\n")

    print(f"Report successfully generated at: {report_path}")

if __name__ == "__main__":
    main()
