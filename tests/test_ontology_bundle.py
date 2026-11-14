"""Offline tests for source-bound Auto-Ontology bundle generation."""
from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
for path in (REPO_ROOT / "tools" / "infra", REPO_ROOT / "src", REPO_ROOT):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

import build_ontology_bundle as bundle  # noqa: E402
from igf.graph.decl_schema import decl_key, edge_key  # noqa: E402


class OfflineBundleTests(unittest.TestCase):
    def _source_index(self, directory: Path) -> tuple[Path, str, str]:
        index = directory / "index"
        index.mkdir()
        a = "InfoGeometry.Meta.ArchetypeA"
        b = "InfoGeometry.Meta.ArchetypeB"
        decls = [
            {"_key": decl_key(a), "name": a, "module": "InfoGeometry.Meta",
             "kind": "structure", "doc": "Candidate type", "relFile": "src/InfoGeometry/Meta/A.lean", "line": 4},
            {"_key": decl_key(b), "name": b, "module": "InfoGeometry.Meta",
             "kind": "theorem", "doc": "A theorem", "relFile": "src/InfoGeometry/Meta/A.lean", "line": 9},
        ]
        edges = [{"_key": edge_key(b, "type", a), "src": b, "dst": a, "kind": "type"}]
        decl_path, edge_path = index / "decls.jsonl", index / "edges.jsonl"
        decl_path.write_text("".join(json.dumps(row) + "\n" for row in decls), encoding="utf-8")
        edge_path.write_text("".join(json.dumps(row) + "\n" for row in edges), encoding="utf-8")
        source_hash, olean_hash = "a" * 64, "b" * 64
        meta = {
            "schemaVersion": 3,
            "importRoot": "InfoGeometry.All",
            "nsFilter": "InfoGeometry",
            "sourceHash": source_hash,
            "oleanHash": olean_hash,
            "outputHashAlgorithm": "sha256",
            "outputHashes": {
                "decls.jsonl": hashlib.sha256(decl_path.read_bytes()).hexdigest(),
                "edges.jsonl": hashlib.sha256(edge_path.read_bytes()).hexdigest(),
            },
        }
        (index / "meta.json").write_text(json.dumps(meta), encoding="utf-8")
        return index, source_hash, olean_hash

    def test_builds_source_bound_terms_memberships_and_relations(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            index, source_hash, olean_hash = self._source_index(root)
            output = root / "bundle"
            with patch.object(bundle, "compute_lean_source_hash", return_value=source_hash), \
                 patch.object(bundle, "compute_olean_content_hash", return_value=olean_hash):
                receipt = bundle.build_bundle(index, output, repo_root=root)

            self.assertEqual(receipt["schema"], bundle.BUNDLE_SCHEMA)
            self.assertEqual(receipt["counts"], {
                "terms": 2, "module_memberships": 2, "relationships": 1, "modules": 1,
            })
            self.assertEqual(set(path.name for path in output.iterdir()), {
                "terms.jsonl", "module_memberships.jsonl", "relationships.jsonl", "bundle_receipt.json",
            })
            terms = [json.loads(line) for line in (output / "terms.jsonl").read_text().splitlines()]
            self.assertEqual({row["name"] for row in terms}, {
                "InfoGeometry.Meta.ArchetypeA", "InfoGeometry.Meta.ArchetypeB",
            })
            relations = [json.loads(line) for line in (output / "relationships.jsonl").read_text().splitlines()]
            self.assertEqual(relations[0]["kind"], "type")
            self.assertEqual(relations[0]["src_imported_id"], decl_key("InfoGeometry.Meta.ArchetypeB"))

    def test_rejects_stale_source_export(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            index, _source_hash, olean_hash = self._source_index(root)
            with patch.object(bundle, "compute_lean_source_hash", return_value="c" * 64), \
                 patch.object(bundle, "compute_olean_content_hash", return_value=olean_hash):
                with self.assertRaisesRegex(ValueError, "sourceHash is stale"):
                    bundle.build_bundle(index, root / "bundle", repo_root=root)

    def test_refuses_to_overwrite_existing_bundle(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            index, source_hash, olean_hash = self._source_index(root)
            output = root / "bundle"
            output.mkdir()
            marker = output / "keep.txt"
            marker.write_text("preserve", encoding="utf-8")
            with patch.object(bundle, "compute_lean_source_hash", return_value=source_hash), \
                 patch.object(bundle, "compute_olean_content_hash", return_value=olean_hash):
                with self.assertRaises(FileExistsError):
                    bundle.build_bundle(index, output, repo_root=root)
            self.assertEqual(marker.read_text(encoding="utf-8"), "preserve")

    def test_rejects_dangling_dependency(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            index, source_hash, olean_hash = self._source_index(root)
            edge_path = index / "edges.jsonl"
            edge_path.write_text(json.dumps({
                "src": "InfoGeometry.Meta.ArchetypeB",
                "dst": "InfoGeometry.Missing",
                "kind": "value",
            }) + "\n", encoding="utf-8")
            meta_path = index / "meta.json"
            meta = json.loads(meta_path.read_text(encoding="utf-8"))
            meta["outputHashes"]["edges.jsonl"] = hashlib.sha256(edge_path.read_bytes()).hexdigest()
            meta_path.write_text(json.dumps(meta), encoding="utf-8")
            with patch.object(bundle, "compute_lean_source_hash", return_value=source_hash), \
                 patch.object(bundle, "compute_olean_content_hash", return_value=olean_hash):
                with self.assertRaisesRegex(ValueError, "dangling compiler dependency"):
                    bundle.build_bundle(index, root / "bundle", repo_root=root)


if __name__ == "__main__":
    unittest.main()
