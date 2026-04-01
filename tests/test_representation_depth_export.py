import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
EXPORTER = REPO_ROOT / "lean" / "DAG" / "RepresentationDepthExport.lean"
IMPORT_MODULES = os.environ.get("REP_DEPTH_IMPORTS", "InfoGeometry.Audit")


def _render_name(x) -> str:
    if isinstance(x, str):
        return x
    return json.dumps(x, ensure_ascii=False, sort_keys=True)


def _load_export():
    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "representation-depth-tags.json"
        cmd = [
            "lake",
            "env",
            "lean",
            "--run",
            str(EXPORTER),
            IMPORT_MODULES,
            str(out),
        ]
        proc = subprocess.run(
            cmd,
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
        )
        if proc.returncode != 0:
            raise AssertionError(
                "exporter failed\n"
                f"cmd: {' '.join(cmd)}\n"
                f"stdout:\n{proc.stdout}\n"
                f"stderr:\n{proc.stderr}"
            )
        if not out.exists():
            raise AssertionError(f"expected output file was not written: {out}")

        payload = json.loads(out.read_text(encoding="utf-8"))
        return payload, proc


def _rows_by_name(rows):
    return {_render_name(row["name"]): row for row in rows}


def _find_row(rows, needle: str):
    matches = [row for row in rows if needle in _render_name(row["name"])]
    if not matches:
        raise AssertionError(f"could not find row containing declaration name: {needle}")
    if len(matches) > 1:
        names = [_render_name(r["name"]) for r in matches]
        raise AssertionError(f"ambiguous row lookup for {needle}: {names}")
    return matches[0]


class RepresentationDepthExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload, cls.proc = _load_export()
        cls.rows = cls.payload["declarations"]
        cls.rows_by_name = _rows_by_name(cls.rows)

    def test_top_level_contract(self):
        payload = self.payload
        self.assertIn("count", payload)
        self.assertIn("declarations", payload)
        self.assertIsInstance(payload["count"], int)
        self.assertIsInstance(payload["declarations"], list)
        self.assertEqual(payload["count"], len(payload["declarations"]))
        self.assertGreater(payload["count"], 0)

    def test_row_surface_contains_upgraded_fields(self):
        required = {
            "name",
            "module",
            "kind",
            "depth",
            "depthNat",
            "sourceDepthNat",
            "effectiveSourceDepthNat",
            "targetDepthNat",
            "directTaggedDeps",
            "closureTaggedDeps",
            "directTaggedDepCount",
            "closureTaggedDepCount",
            "directDepDepthNats",
            "closureDepDepthNats",
            "minDirectDepth",
            "maxDirectDepth",
            "minClosureDepth",
            "maxClosureDepth",
            "nearestLowerDirectDepth",
            "shallowestLowerDirectDepth",
            "nearestLowerClosureDepth",
            "shallowestLowerClosureDepth",
            "reachesPrevDirect",
            "reachesBelowPrevDirect",
            "reachesAboveDirect",
            "reachesPrevClosure",
            "reachesBelowPrevClosure",
            "reachesAboveClosure",
            "judgment",
            "capstone",
        }

        for row in self.rows:
            missing = required.difference(row.keys())
            self.assertFalse(
                missing,
                msg=f"row {_render_name(row['name'])} is missing keys: {sorted(missing)}",
            )

    def test_counts_match_arrays(self):
        for row in self.rows:
            self.assertEqual(
                row["directTaggedDepCount"],
                len(row["directTaggedDeps"]),
                msg=_render_name(row["name"]),
            )
            self.assertEqual(
                row["closureTaggedDepCount"],
                len(row["closureTaggedDeps"]),
                msg=_render_name(row["name"]),
            )

    def test_min_max_fields_match_depth_arrays(self):
        for row in self.rows:
            direct = row["directDepDepthNats"]
            closure = row["closureDepDepthNats"]

            if direct:
                self.assertEqual(row["minDirectDepth"], min(direct), msg=_render_name(row["name"]))
                self.assertEqual(row["maxDirectDepth"], max(direct), msg=_render_name(row["name"]))
            else:
                self.assertIsNone(row["minDirectDepth"], msg=_render_name(row["name"]))
                self.assertIsNone(row["maxDirectDepth"], msg=_render_name(row["name"]))

            if closure:
                self.assertEqual(row["minClosureDepth"], min(closure), msg=_render_name(row["name"]))
                self.assertEqual(row["maxClosureDepth"], max(closure), msg=_render_name(row["name"]))
            else:
                self.assertIsNone(row["minClosureDepth"], msg=_render_name(row["name"]))
                self.assertIsNone(row["maxClosureDepth"], msg=_render_name(row["name"]))

    def test_nearest_and_shallowest_lower_depths_are_consistent(self):
        for row in self.rows:
            target = row["targetDepthNat"]

            direct_lowers = sorted(d for d in row["directDepDepthNats"] if d < target)
            closure_lowers = sorted(d for d in row["closureDepDepthNats"] if d < target)

            expected_nearest_direct = direct_lowers[-1] if direct_lowers else None
            expected_shallowest_direct = direct_lowers[0] if direct_lowers else None
            expected_nearest_closure = closure_lowers[-1] if closure_lowers else None
            expected_shallowest_closure = closure_lowers[0] if closure_lowers else None

            self.assertEqual(
                row["nearestLowerDirectDepth"],
                expected_nearest_direct,
                msg=_render_name(row["name"]),
            )
            self.assertEqual(
                row["shallowestLowerDirectDepth"],
                expected_shallowest_direct,
                msg=_render_name(row["name"]),
            )
            self.assertEqual(
                row["nearestLowerClosureDepth"],
                expected_nearest_closure,
                msg=_render_name(row["name"]),
            )
            self.assertEqual(
                row["shallowestLowerClosureDepth"],
                expected_shallowest_closure,
                msg=_render_name(row["name"]),
            )

    def test_closure_is_strict_and_does_not_include_self(self):
        for row in self.rows:
            self_name = _render_name(row["name"])
            closure_names = {_render_name(x) for x in row["closureTaggedDeps"]}
            self.assertNotIn(
                self_name,
                closure_names,
                msg=f"strict closure violated for {self_name}",
            )

    def test_effective_source_depth_is_exact_nearest_lower_or_target(self):
        for row in self.rows:
            nearest = row["nearestLowerDirectDepth"]
            target = row["targetDepthNat"]
            expected = target if nearest is None else nearest
            self.assertEqual(
                row["effectiveSourceDepthNat"],
                expected,
                msg=_render_name(row["name"]),
            )

    def test_known_transport_row_distinguishes_immediate_vs_deep_reach(self):
        row = _find_row(self.rows, "transportDirac_sq_eq_transportMetricOp")

        self.assertEqual(row["nearestLowerDirectDepth"], 3)
        self.assertEqual(row["nearestLowerClosureDepth"], 3)
        self.assertEqual(row["shallowestLowerClosureDepth"], 2)
        self.assertNotEqual(
            row["nearestLowerClosureDepth"],
            row["shallowestLowerClosureDepth"],
        )


if __name__ == "__main__":
    unittest.main()
