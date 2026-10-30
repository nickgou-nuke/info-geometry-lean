"""Renderer integration boundaries: source binding, escaping and local assets."""

from contextlib import redirect_stderr, redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest

from tools.repository_evolution import render_explorer


class EvolutionRenderTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.data = self.root / "input.json"
        self.data.write_text(json.dumps({
            "schema": "repo-phylogeny/v1",
            "subject": "</script><script>untrusted()</script>",
        }), encoding="utf-8")
        self.out = self.root / "output" / "repository-phylogeny.html"

    def run_renderer(self, *extra):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            render_explorer.main([
                "--data", str(self.data), "--out", str(self.out), *extra,
            ])

    def make_report(self, successful=True):
        path = self.root / "hodge.json"
        path.write_text(json.dumps({
            "schema": "ancestry-hodge/v1",
            "source": {"sha256": hashlib.sha256(self.data.read_bytes()).hexdigest()},
            "checks": {"D_is_symmetric": successful},
            "all_exact_checks_passed": successful,
        }), encoding="utf-8")
        return path

    def test_embeds_safe_json_and_copies_offline_companion(self):
        self.run_renderer()
        rendered = self.out.read_text(encoding="utf-8")
        self.assertNotIn("</script><script>untrusted()", rendered)
        self.assertIn(r"\u003c/script>", rendered)
        self.assertNotIn("__PHYLOGENY_DATA__", rendered)
        self.assertNotIn("__HODGE_DATA__", rendered)
        source = Path(render_explorer.__file__).with_name("dna-affinity-viewer.html")
        self.assertEqual((self.out.parent / source.name).read_bytes(), source.read_bytes())

    def test_accepts_phylogeny_v2_with_git_object_provenance(self):
        self.data.write_text(json.dumps({
            "schema": "repo-phylogeny/v2",
            "source": {"git_object_format": "sha1"},
            "commits": [{"tree_hash": "a" * 40, "author_time": 1, "committer_time": 2}],
        }), encoding="utf-8")
        self.run_renderer()
        self.assertIn('"repo-phylogeny/v2"', self.out.read_text(encoding="utf-8"))

    def test_embeds_report_bound_to_exact_input_bytes(self):
        self.run_renderer("--hodge", str(self.make_report()))
        self.assertIn('"all_exact_checks_passed":true', self.out.read_text())

    def test_rejects_stale_report_before_writing(self):
        report = self.make_report()
        self.data.write_bytes(self.data.read_bytes() + b"\n")
        with self.assertRaises(SystemExit):
            self.run_renderer("--hodge", str(report))
        self.assertFalse(self.out.exists())

    def test_rejects_report_with_failed_checks(self):
        with self.assertRaises(SystemExit):
            self.run_renderer("--hodge", str(self.make_report(False)))
        self.assertFalse(self.out.exists())

    def test_refuses_to_overwrite_source_input(self):
        original = self.data.read_bytes()
        self.out = self.data
        with self.assertRaises(SystemExit):
            self.run_renderer()
        self.assertEqual(self.data.read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
