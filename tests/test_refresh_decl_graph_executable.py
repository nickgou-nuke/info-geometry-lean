"""Check the exporter artifact, not the environment-prefix executable."""

from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

from tools.infra import refresh_decl_graph as refresh


class RefreshExecutableTests(unittest.TestCase):
    def test_prefixed_command_accepts_existing_indexer_without_mutation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            executable = root / ".lake/build/bin/dagIndexer"
            executable.parent.mkdir(parents=True)
            executable.touch()
            arango = Mock()
            db = arango.ArangoClient.return_value.db.return_value
            db.has_collection.return_value = True
            with (
                patch.object(refresh, "load_repo_arango_env"),
                patch.object(refresh.subprocess, "run", return_value=Mock(stdout="/dependency/lib")),
                patch.object(refresh, "arango_endpoint", return_value="http://unused"),
                patch.object(refresh, "arango_username", return_value="test"),
                patch.object(refresh, "arango_password", return_value="test"),
                patch.dict(sys.modules, {"arango": arango}),
            ):
                result = refresh.stream_to_arango(root, "InfoGeometry.All", "InfoGeometry",
                                                 "test", "exe", "already_exists", "a" * 64)
            self.assertEqual(result, 2)
            db.has_collection.assert_called_once_with("decls_g_already_exists")
            db.create_collection.assert_not_called()
            db.collection.assert_not_called()

    def test_missing_indexer_stops_before_database_access(self):
        with tempfile.TemporaryDirectory() as directory:
            arango = Mock()
            with (
                patch.object(refresh, "load_repo_arango_env"),
                patch.object(refresh.subprocess, "run", return_value=Mock(stdout="/dependency/lib")),
                patch.dict(sys.modules, {"arango": arango}),
            ):
                result = refresh.stream_to_arango(Path(directory), "InfoGeometry.All",
                                                 "InfoGeometry", "test", "exe", "new", "a" * 64)
            self.assertEqual(result, 1)
            arango.ArangoClient.assert_not_called()


if __name__ == "__main__":
    unittest.main()
