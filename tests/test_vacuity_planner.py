import importlib.util
import sys
import unittest
from collections import Counter, defaultdict
from pathlib import Path
from types import ModuleType
from typing import Any, cast


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools.planner.matching import resolve_decl_match, seed_decl_match_context
from tools.planner.policy import cluster_rank_weight, planner_policy_snapshot, precheck_status_priority


def _load_planner_module() -> ModuleType:
    module_path = REPO_ROOT / "tools" / "vacuity_planner.py"
    spec = importlib.util.spec_from_file_location("vacuity_planner", module_path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Unable to load vacuity_planner module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module

planner = _load_planner_module()

JsonObj = dict[str, Any]


class VacuityPlannerTests(unittest.TestCase):
    def test_planner_policy_snapshot_is_explicit(self):
        snapshot = planner_policy_snapshot()

        self.assertEqual(snapshot.get("version"), "v1")
        self.assertEqual(snapshot.get("corridorParticipationDecayModel"), "harmonic")
        self.assertEqual(snapshot.get("replacementClusterParticipationLimit"), 3)
        self.assertEqual(snapshot.get("admissibilityReplacementWindow"), 3)

    def test_planner_policy_helpers_preserve_current_calibration(self):
        self.assertEqual(cluster_rank_weight(1), 1.0)
        self.assertEqual(cluster_rank_weight(2), 0.5)
        self.assertAlmostEqual(cluster_rank_weight(3), 1.0 / 3.0, places=6)
        self.assertEqual(precheck_status_priority("blocked"), 0)
        self.assertEqual(precheck_status_priority("needs-review"), 1)
        self.assertEqual(precheck_status_priority("provisionally-admissible"), 2)
        self.assertEqual(precheck_status_priority("unknown"), -1)

    def _bridge_payload(
        self,
        *,
        source_file_rel: str,
        decl_name: str | None,
        module: str | None,
        line: int | None,
        fingerprint: str,
        head: str,
    ) -> JsonObj:
        source_uri = (REPO_ROOT / source_file_rel).resolve().as_uri()
        payload: JsonObj = {
            "diagnostics": [],
            "goals": [
                {
                    "targetHead": head,
                    "targetHeadSource": "exprSemantic",
                    "targetHeadFingerprint": fingerprint,
                }
            ],
            "responseMeta": {
                "sessionId": {
                    "value": source_uri,
                }
            },
            "theoremTypeHead": head,
            "theoremTypeHeadSource": "exprSemantic",
            "theoremTypeHeadFingerprint": fingerprint,
            "theoremTypeExprFingerprint": {
                "semanticHead": head,
                "fingerprintSource": "exprSemantic",
                "fingerprintV1": fingerprint,
                "exprKind": "const",
                "appArity": 0,
                "binderDepth": 0,
            },
        }
        request: JsonObj = {}
        if decl_name is not None:
            request["declName"] = decl_name
        if module is not None:
            request["module"] = module
        if line is not None:
            request["line"] = line
        request["file"] = source_uri
        if request:
            payload["request"] = request
        return payload

    def test_payload_decl_name_maps_to_declaration_signal(self):
        theorem_entries: list[JsonObj] = [
            {
                "kind": "theorem",
                "name": "InfoGeometry.Canonical.A",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
            }
        ]
        decls: dict[str, JsonObj] = {
            "InfoGeometry.Canonical.A": {
                "name": "InfoGeometry.Canonical.A",
                "kind": "theorem",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 10,
            }
        }
        ctx = planner.build_decl_match_context(theorem_entries, decls, REPO_ROOT)
        payload = self._bridge_payload(
            source_file_rel="lean/InfoGeometry/Canonical/A.lean",
            decl_name="InfoGeometry.Canonical.A",
            module="InfoGeometry.Canonical.A",
            line=9,
            fingerprint="shape/v1/head:const:eq",
            head="Eq",
        )

        observations = planner.observe_bridge_payload(payload, REPO_ROOT / "tmp" / "payload.json", REPO_ROOT, ctx)
        summary, _, decl_signals = planner.normalize_bridge_observations(observations)

        self.assertEqual(summary.get("declarationSignalCount"), 1)
        self.assertIn("InfoGeometry.Canonical.A", decl_signals)
        signal = decl_signals["InfoGeometry.Canonical.A"]
        prov_counts = signal.get("matchProvenanceCounts")
        self.assertIsInstance(prov_counts, dict)
        self.assertGreaterEqual(int(prov_counts.get("exactDecl", 0)), 1)

    def test_payload_without_name_uses_lower_reliability_fallback(self):
        theorem_entries: list[JsonObj] = [
            {
                "kind": "theorem",
                "name": "InfoGeometry.Canonical.A",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
            },
            {
                "kind": "theorem",
                "name": "InfoGeometry.Canonical.B",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
            },
        ]
        decls: dict[str, JsonObj] = {
            "InfoGeometry.Canonical.A": {
                "name": "InfoGeometry.Canonical.A",
                "kind": "theorem",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 10,
            },
            "InfoGeometry.Canonical.B": {
                "name": "InfoGeometry.Canonical.B",
                "kind": "theorem",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 20,
            },
        }
        ctx = planner.build_decl_match_context(theorem_entries, decls, REPO_ROOT)

        payload_explicit = self._bridge_payload(
            source_file_rel="lean/InfoGeometry/Canonical/A.lean",
            decl_name="InfoGeometry.Canonical.A",
            module="InfoGeometry.Canonical.A",
            line=9,
            fingerprint="shape/v1/head:const:eq",
            head="Eq",
        )
        payload_fallback = self._bridge_payload(
            source_file_rel="lean/InfoGeometry/Canonical/A.lean",
            decl_name=None,
            module="InfoGeometry.Canonical.A",
            line=9,
            fingerprint="shape/v1/head:const:eq",
            head="Eq",
        )

        observations: list[JsonObj] = []
        observations.extend(
            planner.observe_bridge_payload(payload_explicit, REPO_ROOT / "tmp" / "payload-explicit.json", REPO_ROOT, ctx)
        )
        fallback_observations = planner.observe_bridge_payload(
            payload_fallback,
            REPO_ROOT / "tmp" / "payload-fallback.json",
            REPO_ROOT,
            ctx,
        )
        observations.extend(fallback_observations)

        fallback_matches = [
            obs
            for obs in fallback_observations
            if obs.get("declName") == "InfoGeometry.Canonical.A"
        ]
        self.assertGreater(len(fallback_matches), 0)
        self.assertTrue(
            any(
                obs.get("declMatchProvenance") in {"locationFallback", "fingerprintFallback"}
                and float(obs.get("declMatchReliability", 1.0)) < 1.0
                for obs in fallback_matches
            )
        )

        _, _, decl_signals = planner.normalize_bridge_observations(observations)
        signal = decl_signals["InfoGeometry.Canonical.A"]
        prov_counts = signal.get("matchProvenanceCounts")
        self.assertIsInstance(prov_counts, dict)
        self.assertGreaterEqual(int(prov_counts.get("exactDecl", 0)), 1)
        self.assertGreaterEqual(
            int(prov_counts.get("locationFallback", 0)) + int(prov_counts.get("fingerprintFallback", 0)),
            1,
        )

    def test_location_fallback_uses_nearest_declaration_window(self):
        theorem_entries: list[JsonObj] = [
            {
                "kind": "theorem",
                "name": "InfoGeometry.Canonical.A",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
                "line": 100,
            },
            {
                "kind": "theorem",
                "name": "InfoGeometry.Canonical.B",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
                "line": 220,
            },
        ]
        decls: dict[str, JsonObj] = {
            "InfoGeometry.Canonical.A": {
                "name": "InfoGeometry.Canonical.A",
                "kind": "theorem",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 100,
            },
            "InfoGeometry.Canonical.B": {
                "name": "InfoGeometry.Canonical.B",
                "kind": "theorem",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 220,
            },
        }
        ctx = planner.build_decl_match_context(theorem_entries, decls, REPO_ROOT)

        payload = self._bridge_payload(
            source_file_rel="lean/InfoGeometry/Canonical/A.lean",
            decl_name=None,
            module="InfoGeometry.Canonical.A",
            line=150,
            fingerprint="shape/v1/head:const:eq",
            head="Eq",
        )
        source_file = "lean/InfoGeometry/Canonical/A.lean"
        decl_name, provenance, reliability = resolve_decl_match(
            payload,
            source_file=source_file,
            root=REPO_ROOT,
            match_ctx=ctx,
        )

        self.assertEqual(decl_name, "InfoGeometry.Canonical.A")
        self.assertEqual(provenance, "locationFallback")
        self.assertLess(float(reliability), 1.0)

    def test_location_fallback_prefers_true_nearest_declaration(self):
        theorem_entries: list[JsonObj] = [
            {
                "kind": "theorem",
                "name": "InfoGeometry.Canonical.A",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
                "line": 100,
            },
            {
                "kind": "theorem",
                "name": "InfoGeometry.Canonical.B",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
                "line": 220,
            },
        ]
        decls: dict[str, JsonObj] = {
            "InfoGeometry.Canonical.A": {
                "name": "InfoGeometry.Canonical.A",
                "kind": "theorem",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 100,
            },
            "InfoGeometry.Canonical.B": {
                "name": "InfoGeometry.Canonical.B",
                "kind": "theorem",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 220,
            },
        }
        ctx = planner.build_decl_match_context(theorem_entries, decls, REPO_ROOT)

        payload = self._bridge_payload(
            source_file_rel="lean/InfoGeometry/Canonical/A.lean",
            decl_name=None,
            module="InfoGeometry.Canonical.A",
            line=190,
            fingerprint="shape/v1/head:const:eq",
            head="Eq",
        )

        decl_name, provenance, _ = resolve_decl_match(
            payload,
            source_file="lean/InfoGeometry/Canonical/A.lean",
            root=REPO_ROOT,
            match_ctx=ctx,
        )

        self.assertEqual(decl_name, "InfoGeometry.Canonical.B")
        self.assertEqual(provenance, "locationFallback")

    def test_decl_extraction_ignores_unrelated_nested_name_file_line(self):
        theorem_entries: list[JsonObj] = [
            {
                "kind": "theorem",
                "name": "InfoGeometry.Canonical.A",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
                "line": 100,
            },
            {
                "kind": "theorem",
                "name": "InfoGeometry.Canonical.B",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
                "line": 220,
            },
        ]
        decls: dict[str, JsonObj] = {
            "InfoGeometry.Canonical.A": {
                "name": "InfoGeometry.Canonical.A",
                "kind": "theorem",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 100,
            },
            "InfoGeometry.Canonical.B": {
                "name": "InfoGeometry.Canonical.B",
                "kind": "theorem",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 220,
            },
        }
        ctx = planner.build_decl_match_context(theorem_entries, decls, REPO_ROOT)

        payload = self._bridge_payload(
            source_file_rel="lean/InfoGeometry/Canonical/A.lean",
            decl_name="InfoGeometry.Canonical.A",
            module="InfoGeometry.Canonical.A",
            line=100,
            fingerprint="shape/v1/head:const:eq",
            head="Eq",
        )
        payload["goals"] = [
            {
                "name": "InfoGeometry.Canonical.B",
                "file": (REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve().as_uri(),
                "line": 220,
                "targetHead": "Eq",
                "targetHeadSource": "exprSemantic",
                "targetHeadFingerprint": "shape/v1/head:const:eq",
            }
        ]

        decl_name, provenance, _ = resolve_decl_match(
            payload,
            source_file="lean/InfoGeometry/Canonical/A.lean",
            root=REPO_ROOT,
            match_ctx=ctx,
        )

        self.assertEqual(decl_name, "InfoGeometry.Canonical.A")
        self.assertEqual(provenance, "exactDecl")

    def test_normalization_builds_declaration_signal_index(self):
        observations: list[JsonObj] = [
            {
                "surface": "target",
                "semanticHead": "Eq",
                "headSource": "exprSemantic",
                "fingerprintV1": "fp:eq",
                "exprKind": "app",
                "arityShape": "arity:2+",
                "binderShape": "binder:0",
                "sourceFile": "lean/InfoGeometry/Canonical/A.lean",
                "declName": "InfoGeometry.A",
                "diagnosticProvenance": ["leanTag"],
                "observationConfidence": 0.92,
            }
        ]

        summary, file_signals, decl_signals = planner.normalize_bridge_observations(observations)

        self.assertEqual(summary.get("declarationSignalCount"), 1)
        self.assertIn("lean/InfoGeometry/Canonical/A.lean", file_signals)
        self.assertIn("InfoGeometry.A", decl_signals)
        decl_signal = decl_signals["InfoGeometry.A"]
        self.assertEqual(decl_signal.get("semanticCount"), 1)
        self.assertEqual(decl_signal.get("fingerprintCount"), 1)

    def test_rank_vacuity_prefers_declaration_scope_profile(self):
        theorem_entries: list[JsonObj] = [
            {
                "kind": "theorem",
                "name": "InfoGeometry.A",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
                "tags": ["wrapper-candidate"],
                "violations": [{"level": "warning", "code": "V1/public-wrapper-inflation"}],
                "reverse_type": 0,
                "reverse_value": 0,
                "is_sink": True,
            }
        ]
        module_region = {"InfoGeometry.Canonical.A": "canonical"}
        file_region = {"lean/InfoGeometry/Canonical/A.lean": "canonical"}
        bridge_file_signals: dict[str, JsonObj] = {
            "lean/InfoGeometry/Canonical/A.lean": {
                "semanticCount": 1,
                "fingerprintCount": 1,
                "avgConfidence": 0.52,
                "semanticHeadCounts": [["Eq", 1]],
                "fingerprintCounts": [["fp:file", 1]],
                "exprKindCounts": [["app", 1]],
                "arityShapeCounts": [["arity:1", 1]],
                "binderShapeCounts": [["binder:0", 1]],
                "clusterKeys": [["fp:fp:file|head:Eq|kind:app|arity:1|binder:0", 1]],
            }
        }
        bridge_decl_signals: dict[str, JsonObj] = {
            "InfoGeometry.A": {
                "semanticCount": 3,
                "fingerprintCount": 2,
                "avgConfidence": 0.94,
                "avgMappingReliability": 0.94,
                "semanticHeadCounts": [["Eq", 3]],
                "fingerprintCounts": [["fp:decl", 2]],
                "exprKindCounts": [["app", 3]],
                "arityShapeCounts": [["arity:2+", 3]],
                "binderShapeCounts": [["binder:0", 3]],
                "clusterKeys": [["fp:fp:decl|head:Eq|kind:app|arity:2+|binder:0", 2]],
                "matchProvenanceCounts": {"exactDecl": 3},
            }
        }

        ranked = planner.rank_vacuity_candidates(
            theorem_entries=theorem_entries,
            module_region=module_region,
            file_region=file_region,
            hole_counts={},
            bridge_file_signals=bridge_file_signals,
            bridge_decl_signals=bridge_decl_signals,
            top_k=10,
        )

        self.assertEqual(len(ranked), 1)
        profile = ranked[0].get("semanticProfile")
        self.assertIsInstance(profile, dict)
        self.assertEqual(profile.get("scope"), "declaration")
        self.assertEqual(profile.get("mapping"), "exactDecl")

    def test_rank_declaration_plans_emits_corridor_fields(self):
        vacuity_candidates: list[JsonObj] = [
            {
                "name": "InfoGeometry.Wrap",
                "file": "lean/InfoGeometry/Canonical/Wrap.lean",
                "region": "canonical",
                "score": 0.82,
                "confidence": 0.79,
                "semanticProfile": {
                    "clusterKeys": [["fp:fp:eq|head:Eq|kind:app|arity:2+|binder:0", 2]],
                    "semanticHeadCounts": [["Eq", 2]],
                    "fingerprintCounts": [["fp:eq", 2]],
                },
            }
        ]
        owner_candidates: list[JsonObj] = [
            {
                "ownerFile": "lean/InfoGeometry/Canonical/Wrap.lean",
                "region": "canonical",
                "supportingVacuityCandidates": ["InfoGeometry.Wrap"],
                "score": 0.73,
                "confidence": 0.81,
            }
        ]
        replacement_candidates: list[JsonObj] = [
            {
                "replacementDecl": "InfoGeometry.Target",
                "region": "canonical",
                "supportingVacuityCandidates": ["InfoGeometry.Wrap"],
                "ownerCorridor": ["lean/InfoGeometry/Canonical/Wrap.lean"],
                "score": 0.78,
                "confidence": 0.80,
            },
            {
                "replacementDecl": "InfoGeometry.Other",
                "region": "legacy",
                "supportingVacuityCandidates": [],
                "ownerCorridor": [],
                "score": 0.60,
                "confidence": 0.70,
            },
        ]
        bridge_decl_signals: dict[str, JsonObj] = {
            "InfoGeometry.Target": {
                "clusterKeys": [["fp:fp:eq|head:Eq|kind:app|arity:2+|binder:0", 1]],
                "semanticHeadCounts": [["Eq", 1]],
                "fingerprintCounts": [["fp:eq", 1]],
            },
            "InfoGeometry.Other": {
                "clusterKeys": [["fp:fp:neq|head:And|kind:app|arity:2+|binder:0", 1]],
                "semanticHeadCounts": [["And", 1]],
                "fingerprintCounts": [["fp:neq", 1]],
            },
        }

        plans = planner.rank_declaration_plans(
            vacuity_candidates=vacuity_candidates,
            owner_candidates=owner_candidates,
            replacement_candidates=replacement_candidates,
            bridge_decl_signals=bridge_decl_signals,
            top_k=5,
        )

        self.assertEqual(len(plans), 1)
        plan = plans[0]
        self.assertIn("candidate", plan)
        self.assertIn("probable_owner", plan)
        self.assertIn("probable_replacement_corridor", plan)
        self.assertIn("confidence", plan)
        self.assertIn("confidenceProvenance", plan)

        owner = plan.get("probable_owner")
        self.assertIsInstance(owner, dict)
        self.assertEqual(owner.get("ownerFile"), "lean/InfoGeometry/Canonical/Wrap.lean")

        corridor = plan.get("probable_replacement_corridor")
        self.assertIsInstance(corridor, list)
        self.assertGreater(len(corridor), 0)
        first = corridor[0]
        self.assertEqual(first.get("replacementDecl"), "InfoGeometry.Target")

    def test_rank_fingerprint_corridors_groups_vacuity_and_replacements(self):
        cluster_key = "fp:shape/v1/head:const:eq|head:Eq|kind:app|arity:2+|binder:0"
        vacuity_candidates: list[JsonObj] = [
            {
                "name": "InfoGeometry.A",
                "semanticClusterKey": cluster_key,
                "score": 0.88,
                "confidence": 0.79,
                "region": "canonical",
            },
            {
                "name": "InfoGeometry.B",
                "semanticClusterKey": cluster_key,
                "score": 0.81,
                "confidence": 0.74,
                "region": "canonical",
            },
        ]
        replacement_candidates: list[JsonObj] = [
            {
                "replacementDecl": "InfoGeometry.R",
                "score": 0.77,
                "confidence": 0.72,
                "region": "canonical",
            }
        ]
        bridge_decl_signals: dict[str, JsonObj] = {
            "InfoGeometry.R": {
                "clusterKeys": [[cluster_key, 3]],
            }
        }

        corridors = planner.rank_fingerprint_corridors(
            vacuity_candidates=vacuity_candidates,
            replacement_candidates=replacement_candidates,
            bridge_decl_signals=bridge_decl_signals,
            top_k=10,
        )

        self.assertEqual(len(corridors), 1)
        row = corridors[0]
        self.assertEqual(row.get("clusterKey"), cluster_key)
        self.assertEqual(row.get("vacuityCount"), 2)
        self.assertEqual(row.get("replacementCount"), 1)
        vac_rows = row.get("vacuityCandidates")
        self.assertIsInstance(vac_rows, list)
        self.assertEqual(vac_rows[0].get("name"), "InfoGeometry.A")
        repl_rows = row.get("replacementCandidates")
        self.assertIsInstance(repl_rows, list)
        self.assertEqual(repl_rows[0].get("replacementDecl"), "InfoGeometry.R")

    def test_decl_match_context_from_decls_includes_non_theorem_kinds(self):
        theorem_entries: list[JsonObj] = [
            {
                "kind": "theorem",
                "name": "InfoGeometry.Canonical.A",
                "file": "lean/InfoGeometry/Canonical/A.lean",
                "module": "InfoGeometry.Canonical.A",
                "line": 10,
            }
        ]
        decls: dict[str, JsonObj] = {
            "InfoGeometry.Canonical.A": {
                "name": "InfoGeometry.Canonical.A",
                "kind": "theorem",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 10,
            },
            "InfoGeometry.Canonical.Helper": {
                "name": "InfoGeometry.Canonical.Helper",
                "kind": "def",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 36,
            },
            "InfoGeometry.Canonical.Shortcut": {
                "name": "InfoGeometry.Canonical.Shortcut",
                "kind": "abbrev",
                "file": str((REPO_ROOT / "lean/InfoGeometry/Canonical/A.lean").resolve()),
                "module": "InfoGeometry.Canonical.A",
                "line": 42,
            },
        }

        ctx = planner.build_decl_match_context(theorem_entries, decls, REPO_ROOT)
        self.assertIn("declMeta", ctx)
        self.assertIn("declNames", ctx)
        self.assertNotIn("theoremMeta", ctx)
        self.assertNotIn("theoremNames", ctx)

        payload_explicit = self._bridge_payload(
            source_file_rel="lean/InfoGeometry/Canonical/A.lean",
            decl_name="InfoGeometry.Canonical.Helper",
            module="InfoGeometry.Canonical.A",
            line=36,
            fingerprint="shape/v1/head:const:eq",
            head="Eq",
        )
        payload_location = self._bridge_payload(
            source_file_rel="lean/InfoGeometry/Canonical/A.lean",
            decl_name=None,
            module="InfoGeometry.Canonical.A",
            line=35,
            fingerprint="shape/v1/head:const:eq",
            head="Eq",
        )

        explicit_name, explicit_prov, explicit_rel = resolve_decl_match(
            payload_explicit,
            source_file="lean/InfoGeometry/Canonical/A.lean",
            root=REPO_ROOT,
            match_ctx=ctx,
        )
        self.assertEqual(explicit_name, "InfoGeometry.Canonical.Helper")
        self.assertEqual(explicit_prov, "exactDecl")
        self.assertEqual(float(explicit_rel), 1.0)

        location_name, location_prov, _ = resolve_decl_match(
            payload_location,
            source_file="lean/InfoGeometry/Canonical/A.lean",
            root=REPO_ROOT,
            match_ctx=ctx,
        )
        self.assertEqual(location_name, "InfoGeometry.Canonical.Helper")
        self.assertEqual(location_prov, "locationFallback")

    def test_rank_fingerprint_corridors_multi_cluster_replacement_membership(self):
        cluster_a = "fp:shape/a|head:Eq|kind:app|arity:2+|binder:0"
        cluster_b = "fp:shape/b|head:And|kind:app|arity:2+|binder:0"
        cluster_c = "fp:shape/c|head:Or|kind:app|arity:2+|binder:0"
        vacuity_candidates: list[JsonObj] = [
            {
                "name": "InfoGeometry.A",
                "semanticClusterKey": cluster_a,
                "score": 0.88,
                "confidence": 0.79,
                "region": "canonical",
            },
            {
                "name": "InfoGeometry.B",
                "semanticClusterKey": cluster_b,
                "score": 0.81,
                "confidence": 0.74,
                "region": "canonical",
            },
        ]
        replacement_candidates: list[JsonObj] = [
            {
                "replacementDecl": "InfoGeometry.R",
                "score": 0.77,
                "confidence": 0.72,
                "region": "canonical",
            }
        ]
        bridge_decl_signals: dict[str, JsonObj] = {
            "InfoGeometry.R": {
                "clusterKeys": [
                    [cluster_a, 7],
                    [cluster_b, 5],
                    [cluster_c, 3],
                ],
            }
        }

        corridors = planner.rank_fingerprint_corridors(
            vacuity_candidates=vacuity_candidates,
            replacement_candidates=replacement_candidates,
            bridge_decl_signals=bridge_decl_signals,
            top_k=10,
        )

        by_key: dict[str, JsonObj] = {}
        for row_any in corridors:
            if not isinstance(row_any, dict):
                continue
            row = cast(JsonObj, row_any)
            cluster_any = row.get("clusterKey")
            if isinstance(cluster_any, str) and cluster_any:
                by_key[cluster_any] = row
        self.assertIn(cluster_a, by_key)
        self.assertIn(cluster_b, by_key)
        self.assertIn(cluster_c, by_key)

        for cluster in (cluster_a, cluster_b, cluster_c):
            repl_rows_any = by_key[cluster].get("replacementCandidates")
            self.assertIsInstance(repl_rows_any, list)
            if not isinstance(repl_rows_any, list):
                continue
            repl_rows: list[JsonObj] = []
            for item_any in cast(list[Any], repl_rows_any):
                if isinstance(item_any, dict):
                    repl_rows.append(cast(JsonObj, item_any))
            self.assertTrue(
                any(r.get("replacementDecl") == "InfoGeometry.R" for r in repl_rows)
            )

    def test_rank_fingerprint_corridors_decay_secondary_cluster_participation(self):
        cluster_a = "fp:shape/a|head:Eq|kind:app|arity:2+|binder:0"
        cluster_b = "fp:shape/b|head:Eq|kind:app|arity:2+|binder:0"
        cluster_c = "fp:shape/c|head:Eq|kind:app|arity:2+|binder:0"

        corridors = planner.rank_fingerprint_corridors(
            vacuity_candidates=[],
            replacement_candidates=[
                {
                    "replacementDecl": "InfoGeometry.R",
                    "score": 0.90,
                    "confidence": 0.75,
                    "region": "canonical",
                }
            ],
            bridge_decl_signals={
                "InfoGeometry.R": {
                    "clusterKeys": [
                        [cluster_a, 9],
                        [cluster_b, 7],
                        [cluster_c, 5],
                    ]
                }
            },
            top_k=10,
        )

        by_key = {str(row.get("clusterKey")): row for row in corridors}
        self.assertGreater(float(by_key[cluster_a].get("score", 0.0)), float(by_key[cluster_b].get("score", 0.0)))
        self.assertGreater(float(by_key[cluster_b].get("score", 0.0)), float(by_key[cluster_c].get("score", 0.0)))
        self.assertEqual(float(by_key[cluster_a].get("replacementParticipationWeight", 0.0)), 1.0)
        self.assertEqual(float(by_key[cluster_b].get("replacementParticipationWeight", 0.0)), 0.5)
        self.assertAlmostEqual(float(by_key[cluster_c].get("replacementParticipationWeight", 0.0)), 1.0 / 3.0, places=4)

    def test_seed_decl_match_context_skips_fingerprint_fallback(self):
        ctx = {"clusterToDecl": defaultdict(Counter)}
        observations: list[JsonObj] = [
            {
                "declName": "InfoGeometry.Canonical.A",
                "declMatchProvenance": "fingerprintFallback",
                "declMatchReliability": 0.52,
                "fingerprintV1": "shape/v1/head:const:eq",
                "semanticHead": "Eq",
                "exprKind": "const",
                "arityShape": "arity:0",
                "binderShape": "binder:0",
            },
            {
                "declName": "InfoGeometry.Canonical.B",
                "declMatchProvenance": "exactDecl",
                "declMatchReliability": 1.0,
                "fingerprintV1": "shape/v1/head:const:eq",
                "semanticHead": "Eq",
                "exprKind": "const",
                "arityShape": "arity:0",
                "binderShape": "binder:0",
            },
        ]

        seed_decl_match_context(ctx, observations)
        cluster_to_decl = ctx["clusterToDecl"]
        self.assertEqual(len(cluster_to_decl), 1)
        only_counter = next(iter(cluster_to_decl.values()))
        self.assertNotIn("InfoGeometry.Canonical.A", only_counter)
        self.assertEqual(int(only_counter.get("InfoGeometry.Canonical.B", 0)), 1)

    def test_rank_admissibility_prechecks_blocks_kind_mismatch(self):
        declaration_plans: list[JsonObj] = [
            {
                "rank": 1,
                "candidate": "InfoGeometry.Candidate",
                "candidateFile": "lean/InfoGeometry/Canonical/Candidate.lean",
                "candidateRegion": "canonical",
                "score": 0.62,
                "confidence": 0.73,
                "probable_replacement_corridor": [
                    {
                        "replacementDecl": "InfoGeometry.HelperDef",
                        "region": "canonical",
                        "score": 0.55,
                        "confidence": 0.69,
                    }
                ],
            }
        ]
        decls: dict[str, JsonObj] = {
            "InfoGeometry.Candidate": {"name": "InfoGeometry.Candidate", "kind": "theorem"},
            "InfoGeometry.HelperDef": {"name": "InfoGeometry.HelperDef", "kind": "def"},
        }

        rows = planner.rank_admissibility_prechecks(
            declaration_plans=declaration_plans,
            decls=decls,
            bridge_decl_signals={},
            top_k=10,
        )

        self.assertEqual(len(rows), 1)
        row = rows[0]
        self.assertEqual(row.get("precheckStatus"), "blocked")
        self.assertIn("replacement is not theorem-like", row.get("hardFailures", []))

    def test_rank_admissibility_prechecks_marks_provisional_with_shape_overlap(self):
        declaration_plans: list[JsonObj] = [
            {
                "rank": 1,
                "candidate": "InfoGeometry.Candidate",
                "candidateFile": "lean/InfoGeometry/Canonical/Candidate.lean",
                "candidateRegion": "canonical",
                "score": 0.72,
                "confidence": 0.78,
                "probable_replacement_corridor": [
                    {
                        "replacementDecl": "InfoGeometry.Target",
                        "region": "canonical",
                        "score": 0.66,
                        "confidence": 0.77,
                    }
                ],
            }
        ]
        decls: dict[str, JsonObj] = {
            "InfoGeometry.Candidate": {"name": "InfoGeometry.Candidate", "kind": "theorem"},
            "InfoGeometry.Target": {"name": "InfoGeometry.Target", "kind": "theorem"},
        }
        cluster = "fp:shape/v1/head:const:eq|head:Eq|kind:app|arity:2+|binder:0"
        bridge_decl_signals: dict[str, JsonObj] = {
            "InfoGeometry.Candidate": {
                "clusterKeys": [[cluster, 2]],
                "semanticHeadCounts": [["Eq", 2]],
                "fingerprintCounts": [["shape/v1/head:const:eq", 2]],
            },
            "InfoGeometry.Target": {
                "clusterKeys": [[cluster, 1]],
                "semanticHeadCounts": [["Eq", 1]],
                "fingerprintCounts": [["shape/v1/head:const:eq", 1]],
            },
        }

        rows = planner.rank_admissibility_prechecks(
            declaration_plans=declaration_plans,
            decls=decls,
            bridge_decl_signals=bridge_decl_signals,
            top_k=10,
        )

        self.assertEqual(len(rows), 1)
        row = rows[0]
        self.assertEqual(row.get("precheckStatus"), "provisionally-admissible")
        self.assertEqual(row.get("hardFailures"), [])
        self.assertEqual(row.get("softWarnings"), [])
        self.assertGreater(float(row.get("shapeOverlap", 0.0)), 0.5)

    def test_rank_admissibility_prechecks_uses_top_n_replacement_fallback(self):
        cluster = "fp:shape/v1/head:const:eq|head:Eq|kind:app|arity:2+|binder:0"
        declaration_plans: list[JsonObj] = [
            {
                "rank": 1,
                "candidate": "InfoGeometry.Candidate",
                "candidateFile": "lean/InfoGeometry/Canonical/Candidate.lean",
                "candidateRegion": "canonical",
                "score": 0.72,
                "confidence": 0.78,
                "probable_replacement_corridor": [
                    {
                        "replacementDecl": "InfoGeometry.HelperDef",
                        "region": "canonical",
                        "score": 0.80,
                        "confidence": 0.79,
                    },
                    {
                        "replacementDecl": "InfoGeometry.Target",
                        "region": "canonical",
                        "score": 0.68,
                        "confidence": 0.77,
                    },
                ],
            }
        ]
        decls: dict[str, JsonObj] = {
            "InfoGeometry.Candidate": {"name": "InfoGeometry.Candidate", "kind": "theorem"},
            "InfoGeometry.HelperDef": {"name": "InfoGeometry.HelperDef", "kind": "def"},
            "InfoGeometry.Target": {"name": "InfoGeometry.Target", "kind": "theorem"},
        }
        bridge_decl_signals: dict[str, JsonObj] = {
            "InfoGeometry.Candidate": {
                "clusterKeys": [[cluster, 2]],
                "semanticHeadCounts": [["Eq", 2]],
                "fingerprintCounts": [["shape/v1/head:const:eq", 2]],
            },
            "InfoGeometry.Target": {
                "clusterKeys": [[cluster, 1]],
                "semanticHeadCounts": [["Eq", 1]],
                "fingerprintCounts": [["shape/v1/head:const:eq", 1]],
            },
        }

        rows = planner.rank_admissibility_prechecks(
            declaration_plans=declaration_plans,
            decls=decls,
            bridge_decl_signals=bridge_decl_signals,
            top_k=10,
        )

        self.assertEqual(len(rows), 1)
        row = rows[0]
        self.assertEqual(row.get("replacementDecl"), "InfoGeometry.Target")
        self.assertEqual(row.get("replacementCorridorRank"), 2)
        self.assertEqual(row.get("precheckStatus"), "provisionally-admissible")
        considered_any = row.get("replacementCandidatesConsidered")
        self.assertIsInstance(considered_any, list)
        considered = cast(list[JsonObj], considered_any)
        self.assertEqual(considered[0].get("precheckStatus"), "blocked")
        self.assertEqual(considered[1].get("precheckStatus"), "provisionally-admissible")


if __name__ == "__main__":
    unittest.main()
