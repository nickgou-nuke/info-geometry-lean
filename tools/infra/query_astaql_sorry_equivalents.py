import sys
import os
import json
from pathlib import Path
from arango import ArangoClient
sys.path.insert(0, os.path.abspath('.'))
sys.path.insert(0, os.path.abspath('./src'))

from igf.graph.decl_schema import (
    STRUCTURAL_FINGERPRINT_VERSION,
    TERM_DIGEST_VERSION,
)
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

    print("=== ASTAQLHASH Matching-Value-Fingerprint Candidates ===")

    # 2. Define the targeted AQL query. Matching finite hashes produce review
    # candidates only; they are not proof-equivalence classes.
    q = f'''
    FOR d IN decls
      FILTER (d.valueDigest != null AND d.valueDigest.algorithmVersion == "{TERM_DIGEST_VERSION}")
          OR (d.valueFingerprint != null AND d.valueFingerprint.algorithmVersion == "{STRUCTURAL_FINGERPRINT_VERSION}")
      LET name_lower = LOWER(d.name)
      FILTER name_lower LIKE "%sorry%"
          OR name_lower LIKE "%_true%"
          OR name_lower LIKE "%trivial%"
      COLLECT hash = (d.valueDigest.digest || d.canonicalValueHash) INTO targets
      FILTER hash != null
      RETURN {{
        canonicalValueHash: hash,
        targetDeclarations: targets[*].d.name,
        matchingDeclarations: (
          FOR peer IN decls
            FILTER (peer.valueDigest != null AND peer.valueDigest.algorithmVersion == "{TERM_DIGEST_VERSION}" AND peer.valueDigest.digest == hash)
                OR (peer.valueFingerprint != null AND peer.valueFingerprint.algorithmVersion == "{STRUCTURAL_FINGERPRINT_VERSION}" AND peer.canonicalValueHash == hash)
            RETURN peer.name
        )
      }}
    '''

    results = list(db.aql.execute(q))
    
    # 3. Write results to markdown artifact
    report_path = Path("astaqlhash_sorry_equivalents_report.md")
    with open(report_path, "w") as f:
        f.write("# ASTAQLHASH Value-Fingerprint Candidate Report\n\n")
        f.write("This report groups declarations with matching finite value fingerprints. A hash match is a navigation candidate only; it does not establish structural identity, theorem equivalence, or shared proof debt.\n\n")
        
        f.write("## Matching Value-Fingerprint Candidates\n\n")
        for row in results:
            hash_val = row["canonicalValueHash"]
            f.write(f"### Candidate Hash: `{hash_val}`\n\n")
            f.write("Target declarations:\n")
            for decl in row["targetDeclarations"]:
                f.write(f"- `{decl}`\n")
            f.write("\nAll declarations sharing this finite hash (source review required):\n")
            for decl in row["matchingDeclarations"]:
                f.write(f"- `{decl}`\n")
            f.write("\n---\n\n")

    print(f"Report successfully generated at: {report_path}")

if __name__ == "__main__":
    main()
