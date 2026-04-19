import json
import tempfile
import unittest
from pathlib import Path

from tools.infra.representation_depth_from_graph import report_from_dir

REPO_ROOT = Path(__file__).resolve().parents[1]


def _render_name(x) -> str:
    if isinstance(x, str):
        return x
    return json.dumps(x, ensure_ascii=False, sort_keys=True)


def _write_jsonl(path: Path, rows: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(row, ensure_ascii=True, sort_keys=True) + "\n" for row in rows),
        encoding="utf-8",
    )


def _node(name: str, depth: int | None, *, capstone: bool = False) -> dict:
    slugs = ["count", "projective", "operator", "krein", "transport", "thermo"]
    layers = [
        "L0_Count",
        "L1_Projective",
        "L2_Operator",
        "L3_Krein",
        "L4_ModularTransport",
        "L5_ThermodynamicClosure",
    ]
    attrs = {}
    labels = []
    if depth is not None:
        attrs = {
            "rep_depth_nat": depth,
            "rep_depth_slug": slugs[depth],
            "rep_layer": layers[depth],
        }
        labels = [f"rep_depth:{slugs[depth]}", f"rep_depth_nat:{depth}", f"rep_layer:{layers[depth]}"]
    if capstone:
        labels.append("attr:capstone")
    return {
        "_key": name.replace(".", "_"),
        "name": name,
        "module": ".".join(name.split(".")[:-1]),
        "kind": "theorem",
        "attrs": attrs,
        "labels": labels,
        "rep_depth": depth,
        "rep_depth_nat": depth,
        "rep_depth_slug": attrs.get("rep_depth_slug"),
        "rep_layer": attrs.get("rep_layer"),
    }


def _edge(src: str, dst: str) -> dict:
    return {"src": src, "dst": dst, "kind": "uses"}


def _load_export():
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        nodes = [
            _node("InfoGeometry.Canonical.transportDirac_sq_eq_transportMetricOp", 4),
            _node("InfoGeometry.Canonical.kreinBridge", 3),
            _node("InfoGeometry.Canonical.operatorOwner", 2),
            _node("InfoGeometry.Canonical.thermoCapstone", 5, capstone=True),
            _node("Mathlib.External.untyped", None),
        ]
        edges = [
            _edge("InfoGeometry.Canonical.transportDirac_sq_eq_transportMetricOp", "InfoGeometry.Canonical.kreinBridge"),
            _edge("InfoGeometry.Canonical.kreinBridge", "InfoGeometry.Canonical.operatorOwner"),
            _edge("InfoGeometry.Canonical.thermoCapstone", "InfoGeometry.Canonical.transportDirac_sq_eq_transportMetricOp"),
            _edge("InfoGeometry.Canonical.thermoCapstone", "Mathlib.External.untyped"),
        ]
        _write_jsonl(root / "ig_nodes.jsonl", nodes)
        _write_jsonl(root / "ig_edges.jsonl", edges)
        return report_from_dir(root), None


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
