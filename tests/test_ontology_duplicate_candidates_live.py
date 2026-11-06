"""Opt-in read-only AQL regression: no collections are created or modified.

Run with ONTOLOGY_LIVE_TEST=1 and PYTHONPATH=src in the ontology environment.
"""

import os
from pathlib import Path
import unittest


@unittest.skipUnless(os.environ.get("ONTOLOGY_LIVE_TEST") == "1", "requires configured Arango")
class DuplicateCandidateQueryTests(unittest.TestCase):
    def test_candidates_preserve_types_versions_and_closedness(self):
        from igf.graph.decl_schema import STRUCTURAL_FINGERPRINT_VERSION, TERM_DIGEST_VERSION
        from tools.infra.arango_root_to_leaf_topology import (
            arango_target, duplicate_candidate_query, run_aql,
        )

        def modern(name, type_hash="type-a", value_hash="body-a", opened=False):
            return {
                "name": name,
                "typeDigest": {"algorithmVersion": TERM_DIGEST_VERSION,
                               "digest": type_hash, "openTerm": opened},
                "valueDigest": {"algorithmVersion": TERM_DIGEST_VERSION,
                                "digest": value_hash, "openTerm": opened},
            }

        def legacy(name, type_hash="type-a", value_hash="body-a"):
            return {
                "name": name,
                "typeFingerprint": {"algorithmVersion": STRUCTURAL_FINGERPRINT_VERSION},
                "valueFingerprint": {"algorithmVersion": STRUCTURAL_FINGERPRINT_VERSION},
                "canonicalTypeHash": type_hash, "canonicalValueHash": value_hash,
            }

        records = [modern("modern-a"), modern("modern-b"),
                   modern("different-type", type_hash="type-b"),
                   modern("different-body", value_hash="body-b"),
                   legacy("legacy-a"), legacy("legacy-b"),
                   modern("open-a", opened=True), modern("open-b", opened=True)]
        # Even a matching legacy fingerprint must not rescue an open modern term.
        for record in records[-2:]:
            record.update(legacy(record["name"]))
        query = duplicate_candidate_query().replace("FOR d IN @@decls", "FOR d IN @records")
        rows = run_aql(arango_target(Path(__file__).resolve().parents[1]), query,
                       {"records": records})
        self.assertEqual(len(rows), 2)
        groups = {row["algorithmVersion"]: row for row in rows}
        self.assertEqual(groups[TERM_DIGEST_VERSION]["declarations"], ["modern-a", "modern-b"])
        self.assertEqual(groups[STRUCTURAL_FINGERPRINT_VERSION]["declarations"],
                         ["legacy-a", "legacy-b"])
        for row in rows:
            self.assertEqual(row["typeFingerprint"], "type-a")
            self.assertEqual(row["valueFingerprint"], "body-a")
            self.assertEqual(row["count"], 2)


if __name__ == "__main__":
    unittest.main()
