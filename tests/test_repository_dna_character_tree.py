"""Behavioral checks for categorical affinity inference; no external services."""

from copy import deepcopy
from fractions import Fraction
import unittest

from tools.repository_evolution.dna_character_tree import (
    CLAIM_SCOPE,
    InputError,
    PRIMARY_SCHEMA,
    SNAPSHOT_SCHEMA,
    four_point_diagnostic,
    infer_tree,
    neighbor_joining,
    tree_fit_diagnostic,
)


def character(state, version="v1"):
    return {"state": state, "algorithm_version": version}


def profiles(rows):
    return {
        "schema": PRIMARY_SCHEMA,
        "provenance": {"source": "observed profiles; no historical mapping supplied"},
        "taxa": [{"id": taxon_id, "characters": markers} for taxon_id, markers in rows],
    }


def digest(letter, version="lean-expr-debruijn-v4", opened=False):
    return {"algorithmVersion": version, "digest": letter * 64, "nodeCount": 5, "openTerm": opened}


def snapshots():
    return {
        "schema": SNAPSHOT_SCHEMA,
        "provenance": {"database": "user asserted export", "source_verified": False},
        "snapshots": [
            {"generation": "g1", "declarations": [{"name": "Pkg.theorem", "typeDigest": digest("a"), "valueDigest": digest("b")}]},
            {"generation": "g2", "declarations": [{"name": "Pkg.theorem", "typeDigest": digest("a"), "valueDigest": digest("c")}]},
            {"generation": "g3", "declarations": [{"name": "Pkg.theorem", "typeDigest": digest("a"), "valueDigest": digest("b")}]},
        ],
    }


class NeighborJoiningTests(unittest.TestCase):
    def test_known_additive_four_taxon_metric(self):
        names = ["A", "B", "C", "D"]
        matrix = [[0, 2, 6, 6], [2, 0, 6, 6], [6, 6, 0, 2], [6, 6, 2, 0]]
        tree = neighbor_joining(names, matrix)
        self.assertEqual(sorted(Fraction(edge["exact_length"]) for edge in tree["edges"]), [1, 1, 1, 1, 4])
        self.assertEqual(tree_fit_diagnostic(names, matrix, tree)["path_distance_rmse"], 0)
        self.assertEqual(four_point_diagnostic(matrix)["max_residual"], 0)
        self.assertEqual(tree["orientation"], "unrooted")
        self.assertNotIn("root", tree)

    def test_negative_lengths_are_preserved(self):
        matrix = [[0, 1, 1], [1, 0, 5], [1, 5, 0]]
        tree = neighbor_joining(["A", "B", "C"], matrix)
        self.assertEqual(tree["negative_branch_count"], 1)
        self.assertEqual(Fraction(tree["negative_branches"][0]["exact_length"]), Fraction(-3, 2))
        self.assertFalse(tree["negative_lengths_clipped"])
        self.assertTrue(tree_fit_diagnostic(["A", "B", "C"], matrix, tree)["exact_fit"])

    def test_tie_breaking_is_independent_of_input_order(self):
        names = ["A", "B", "C", "D"]
        matrix = [[0, 2, 6, 6], [2, 0, 6, 6], [6, 6, 0, 2], [6, 6, 2, 0]]
        permutation = [3, 1, 0, 2]
        reordered = [[matrix[i][j] for j in permutation] for i in permutation]
        self.assertEqual(neighbor_joining(names, matrix), neighbor_joining([names[i] for i in permutation], reordered))

    def test_nonadditivity_is_reported(self):
        matrix = [[0, 2, 2, 2], [2, 0, 3, 2], [2, 3, 0, 2], [2, 2, 2, 0]]
        diagnostic = four_point_diagnostic(matrix)
        self.assertEqual(diagnostic["max_residual"], 1)
        self.assertEqual(diagnostic["positive_residual_quartets"], 1)


class CharacterProfileTests(unittest.TestCase):
    def test_resolution_reports_identity_after_complete_case_filtering(self):
        data = profiles([
            ("C", {"common": character("x"), "partial": character("different")}),
            ("A", {"common": character("x"), "partial": character("other")}),
            ("B", {"common": character("x")}),
        ])
        result = infer_tree(data)
        resolution = result["diagnostics"]["profile_resolution"]
        self.assertTrue(resolution["all_profiles_identical"])
        self.assertEqual(resolution["indistinguishable_taxon_groups"], [["A", "B", "C"]])
        self.assertEqual(resolution["constant_marker_count"], 1)
        self.assertEqual(resolution["variable_marker_count"], 0)

    def test_resolution_preserves_distinct_ids_with_matching_digest_profiles(self):
        result = infer_tree(snapshots())
        resolution = result["diagnostics"]["profile_resolution"]
        self.assertEqual(resolution["distinct_profile_count"], 2)
        self.assertEqual(resolution["indistinguishable_taxon_groups"], [["g1", "g3"]])
        self.assertFalse(resolution["all_profiles_identical"])
        self.assertEqual(resolution["constant_marker_count"], 1)
        self.assertEqual(resolution["variable_marker_count"], 1)
        self.assertEqual(len(result["taxa"]), 3)

    def test_missing_marker_is_excluded_for_every_pair(self):
        data = profiles([
            ("A", {"common": character("x"), "partial": character("same")}),
            ("B", {"common": character("y"), "partial": character("same")}),
            ("C", {"common": character("x")}),
        ])
        result = infer_tree(data)
        self.assertEqual(result["alignment"]["retained_marker_count"], 1)
        self.assertEqual(result["distance_matrix"]["values"], [[0, 1, 0], [1, 0, 1], [0, 1, 0]])
        excluded = result["alignment"]["excluded_markers"][0]
        self.assertEqual(excluded["missing_taxa"], ["C"])

    def test_empty_profile_does_not_become_zero_distance(self):
        data = profiles([("A", {"m": character("a")}), ("B", {"m": character("b")}), ("C", {})])
        with self.assertRaisesRegex(InputError, "no comparable complete-case"):
            infer_tree(data)

    def test_disjoint_marker_intersection_is_rejected(self):
        data = profiles([(name, {name: character("same")}) for name in ("A", "B", "C")])
        with self.assertRaisesRegex(InputError, "no comparable complete-case"):
            infer_tree(data)

    def test_algorithm_mismatch_excludes_whole_column(self):
        data = profiles([
            ("A", {"keep": character("a"), "different-version": character("same", "v1")}),
            ("B", {"keep": character("b"), "different-version": character("same", "v2")}),
            ("C", {"keep": character("a"), "different-version": character("same", "v1")}),
        ])
        result = infer_tree(data)
        self.assertEqual(result["alignment"]["retained_marker_count"], 1)
        self.assertEqual(result["alignment"]["excluded_markers"][0]["reasons"], ["algorithm_version_mismatch"])

    def test_hashes_are_labels_not_bit_distances(self):
        data = profiles([
            ("A", {"m": character("0" * 64)}),
            ("B", {"m": character("0" * 63 + "1")}),
            ("C", {"m": character("f" * 64)}),
        ])
        result = infer_tree(data)
        self.assertEqual(result["distance_matrix"]["values"], [[0, 1, 1], [1, 0, 1], [1, 1, 0]])

    def test_duplicate_taxon_ids_are_rejected(self):
        data = profiles([(name, {"m": character("a")}) for name in ("A", "A", "C")])
        with self.assertRaisesRegex(InputError, "duplicate taxon"):
            infer_tree(data)


class NativeSnapshotAdapterTests(unittest.TestCase):
    def test_type_and_proof_are_separate_observed_markers(self):
        data = snapshots()
        original = deepcopy(data)
        result = infer_tree(data)
        self.assertEqual(result["alignment"]["retained_marker_count"], 2)
        self.assertEqual([row["marker"] for row in result["alignment"]["retained_markers"]], ["type:Pkg.theorem", "value:Pkg.theorem"])
        self.assertEqual(result["distance_matrix"]["values"], [[0, 0.5, 0], [0.5, 0, 0.5], [0, 0.5, 0]])
        self.assertEqual(result["provenance"], data["provenance"])
        self.assertEqual(data, original)
        self.assertEqual(result["claim_scope"], CLAIM_SCOPE)

    def test_unknown_commit_does_not_block_structural_inference(self):
        data = snapshots()
        data["snapshots"][1]["commit"] = "unmapped-user-assertion"
        result = infer_tree(data)
        self.assertEqual([taxon["id"] for taxon in result["taxa"]], ["g1", "g2", "g3"])
        self.assertFalse(result["historical_binding"]["verified"])
        self.assertFalse(result["historical_binding"]["required_for_inference"])
        self.assertEqual(result["adapter"]["snapshots"][1]["source_identifiers_asserted"]["commit"], "unmapped-user-assertion")

    def test_open_digest_is_unknown_and_coverage_is_reported(self):
        data = snapshots()
        data["snapshots"][1]["declarations"][0]["typeDigest"]["openTerm"] = True
        result = infer_tree(data)
        self.assertEqual(result["alignment"]["retained_marker_count"], 1)
        self.assertEqual(result["alignment"]["excluded_markers"][0]["marker"], "type:Pkg.theorem")
        self.assertEqual(result["adapter"]["snapshots"][1]["open_digest_fields"], 1)

    def test_absent_proof_is_unknown_and_coverage_is_reported(self):
        data = snapshots()
        data["snapshots"][1]["declarations"][0]["valueDigest"] = None
        result = infer_tree(data)
        self.assertEqual(result["alignment"]["retained_marker_count"], 1)
        self.assertEqual(result["adapter"]["snapshots"][1]["absent_digest_fields"], 1)

    def test_namespaces_are_not_automatically_aligned(self):
        data = snapshots()
        for snapshot in data["snapshots"]:
            snapshot["declarations"].append({"name": "Common.anchor", "typeDigest": digest("d"), "valueDigest": None})
        data["snapshots"][1]["declarations"][0]["name"] = "Renamed.theorem"
        result = infer_tree(data)
        self.assertEqual(result["alignment"]["retained_marker_count"], 1)
        self.assertEqual(result["alignment"]["retained_markers"][0]["marker"], "type:Common.anchor")
        self.assertIn("type:Renamed.theorem", [row["marker"] for row in result["alignment"]["excluded_markers"]])

    def test_native_digest_version_mismatch_is_excluded(self):
        data = snapshots()
        data["snapshots"][1]["declarations"][0]["typeDigest"]["algorithmVersion"] = "lean-expr-debruijn-v5"
        result = infer_tree(data)
        self.assertEqual(result["alignment"]["retained_marker_count"], 1)
        self.assertEqual(result["alignment"]["excluded_markers"][0]["reasons"], ["algorithm_version_mismatch"])

    def test_metadata_proxy_rows_are_rejected(self):
        data = snapshots()
        data["snapshots"][0]["declarations"] = [{
            "schema": "hive.packet.expr_fingerprint.v1",
            "decl_name": "Pkg.theorem",
            "feature_counts": {"binder_depth_proxy": 2},
            "provenance": {"method": "metadata_proxy_v1"},
        }]
        with self.assertRaisesRegex(InputError, "metadata proxy"):
            infer_tree(data)

    def test_name_only_rows_are_not_treated_as_dna(self):
        data = snapshots()
        data["snapshots"][0]["declarations"] = [{"name": "Pkg.theorem", "module": "Pkg", "id": 1}]
        with self.assertRaisesRegex(InputError, "lacks native typeDigest"):
            infer_tree(data)

    def test_closed_status_must_be_explicit(self):
        data = snapshots()
        del data["snapshots"][0]["declarations"][0]["typeDigest"]["openTerm"]
        with self.assertRaisesRegex(InputError, "openTerm must explicitly"):
            infer_tree(data)

    def test_malformed_digest_is_rejected(self):
        data = snapshots()
        data["snapshots"][0]["declarations"][0]["typeDigest"]["digest"] = "not-a-sha256"
        with self.assertRaisesRegex(InputError, "64 hexadecimal"):
            infer_tree(data)


if __name__ == "__main__":
    unittest.main()
