"""Focused real-Git tests for ancestry preservation and DNA provenance gates."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tools.repository_evolution import phylogeny_export as exporter


class ExportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.run_git("init", "--quiet")
        self.tree = self.run_git("mktree", input="").strip()
        self.ids = {}
        self.commit("root", "2026-01-01T00:00:00Z")
        self.commit("future_parent", "2026-06-01T00:00:00Z", "root")
        self.commit("skew_child", "2026-02-01T00:00:00Z", "future_parent")
        self.commit("side", "2026-02-02T00:00:00Z", "root")
        self.commit("side_two", "2026-02-03T00:00:00Z", "root")
        self.commit("merge", "2026-02-04T00:00:00Z", "skew_child", "side", "side_two")
        self.commit("hidden_one", "2026-02-05T00:00:00Z", "merge")
        self.commit("hidden_two", "2026-02-06T00:00:00Z", "hidden_one")
        self.commit("tip", "2026-02-07T00:00:00Z", "hidden_two")
        self.commit("tag_only", "2025-12-01T00:00:00Z")
        for name, target in (("main", "tip"), ("feature", "side")):
            self.run_git("update-ref", "refs/remotes/origin/" + name, self.ids[target])
        self.run_git("symbolic-ref", "refs/remotes/origin/HEAD", "refs/remotes/origin/main")
        self.run_git("update-ref", "refs/heads/main", self.ids["tip"])
        self.run_git("symbolic-ref", "HEAD", "refs/heads/main")
        self.run_git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                     "tag", "-a", "historic", "-m", "History", self.ids["tag_only"])
        self.url = "https://github.com/example/fixture"

    def run_git(self, *args, input=None, env=None):
        return subprocess.run(["git", "-C", str(self.repo), *args], input=input,
                              capture_output=True, text=True, check=True, env=env).stdout

    def commit(self, name, date, *parents):
        env = dict(os.environ, GIT_AUTHOR_NAME="Test", GIT_AUTHOR_EMAIL="test@example.invalid",
                   GIT_COMMITTER_NAME="Test", GIT_COMMITTER_EMAIL="test@example.invalid",
                   GIT_AUTHOR_DATE=date, GIT_COMMITTER_DATE=date)
        args = ["commit-tree", self.tree, "-m", name]
        for parent in parents:
            args.extend(["-p", self.ids[parent]])
        self.ids[name] = self.run_git(*args, env=env).strip()

    def export(self, **kwargs):
        return exporter.export(self.repo, kwargs.pop("since", "2026-02-01"),
                               kwargs.pop("until", "2026-02-08"), self.url, **kwargs)

    def dna(self, binding="source-verified", target="hidden_one"):
        sha = self.ids[target]
        return {"schema": "repo-dna-snapshots/v1", "repository": self.url, "snapshots": [{
            "commit": sha, "generation": "fixture-generation",
            "provenance": {"binding": binding, "source_commit": sha, "working_tree_clean": True,
                           "build_fingerprint": "fixture-build", "toolchain": "fixture-toolchain"},
            "declarations": [{"name": "Fixture.term", "module": "Fixture",
                "typeDigest": {"algorithmVersion": "lean-expr-debruijn-v4", "digest": "a" * 64,
                               "nodeCount": 3, "openTerm": False},
                "typeFingerprint": {"algorithmVersion": "lean-expr-structural-v3", "shapeHash": "18446744073709551615"},
                "canonicalTypeHash": "18446744073709551615"}]}]}

    def write_packet(self, packet):
        path = self.repo / "packet.json"
        path.write_text(json.dumps(packet), encoding="utf-8")
        return path

    def test_clock_skew_boundary_and_octopus_merge_are_preserved(self):
        data = self.export()
        self.assertEqual(data["stats"]["commit_count"], 7)
        self.assertEqual(data["stats"]["parent_edges"], 9)
        self.assertEqual(data["stats"]["merge_commits"], 1)
        self.assertEqual(data["stats"]["clock_skew_edges"], 1)
        self.assertEqual(data["stats"]["boundary_nodes"], 2)
        ids = {row["sha"] for row in data["commits"]}
        self.assertIn(self.ids["skew_child"], ids)
        self.assertNotIn(self.ids["future_parent"], ids)
        expected = exporter.Counter((parent, row["sha"], i)
                                    for row in data["commits"] for i, parent in enumerate(row["parents"]))
        self.assertEqual(exporter.expanded_edges(data["links"]), expected)
        merged = [link for link in data["links"] if link["target"] == self.ids["merge"]]
        self.assertEqual({link["parent_index"] for link in merged}, {0, 1, 2})
        self.assertTrue(any(link["hidden_count"] >= 2 for link in data["links"]))
        self.assertTrue(all(row["lane"] == 0 for row in data["commits"] if row["sha"] not in {self.ids["side"], self.ids["side_two"]}))

    def test_annotated_tags_extend_reachable_history_and_symref_is_excluded(self):
        data = self.export(since="2025-01-01", until="2027-01-01")
        self.assertEqual(data["stats"]["branch_refs"], 3)
        self.assertEqual(data["stats"]["tag_refs"], 1)
        self.assertEqual(data["stats"]["commit_count"], 10)
        self.assertEqual(data["stats"]["root_commits"], 2)
        tag = next(row for row in data["source"]["refs"] if row["kind"] == "tag")
        self.assertEqual(tag["sha"], self.ids["tag_only"])
        self.assertIn(self.ids["tag_only"], {row["sha"] for row in data["nodes"]})
        self.assertNotIn("origin/HEAD", {row["name"] for row in data["source"]["refs"]})

    def test_local_and_upstream_only_refs_contribute_reachable_commits(self):
        self.commit("local_only", "2026-01-15T00:00:00Z", "root")
        self.run_git("update-ref", "refs/heads/local-only", self.ids["local_only"])
        self.run_git("update-ref", "refs/remotes/upstream/feature", self.ids["local_only"])

        data = self.export(since="2025-01-01", until="2027-01-01")

        self.assertIn(self.ids["local_only"], {row["sha"] for row in data["commits"]})
        ref_names = {row["name"] for row in data["source"]["refs"]}
        self.assertIn("heads/local-only", ref_names)
        self.assertIn("upstream/feature", ref_names)
        self.assertIn("local branches", data["source"]["ref_scope"])

    def test_shallow_root_recovers_raw_parent_boundary(self):
        (self.repo / ".git" / "shallow").write_text(self.ids["tip"] + "\n", encoding="ascii")
        data = self.export()
        self.assertTrue(data["source"]["is_shallow"])
        tip = next(row for row in data["commits"] if row["sha"] == self.ids["tip"])
        self.assertEqual(tip["parents"], [self.ids["hidden_two"]])
        missing = next(row for row in data["nodes"] if row["sha"] == self.ids["hidden_two"])
        self.assertTrue(missing["boundary"])
        self.assertEqual(missing["boundary_reason"], "unresolved-parent")

    def test_manifest_attested_dna_keeps_observation_and_uint64_string(self):
        data = self.export(dna_path=self.write_packet(self.dna()))
        self.assertEqual(data["stats"]["dna_snapshot_count"], 1)
        self.assertIn(self.ids["hidden_one"], {row["sha"] for row in data["nodes"]})
        self.assertEqual(data["dna"]["snapshots"][0]["declarations"][0]["canonicalTypeHash"], "18446744073709551615")
        unverified = self.export(dna_path=self.write_packet(self.dna(binding="unverified")))
        self.assertEqual(unverified["stats"]["dna_snapshot_count"], 0)
        self.assertEqual(len(unverified["dna"]["unattached"]), 1)
        self.assertNotIn(self.ids["hidden_one"], {row["sha"] for row in unverified["nodes"]})

    def test_invalid_dna_fails_instead_of_attaching(self):
        mutations = [
            lambda s: s.update(commit="0" * 40),
            lambda s: s["provenance"].update(source_commit=self.ids["root"]),
            lambda s: s["declarations"].append(dict(s["declarations"][0])),
            lambda s: s["declarations"][0]["typeDigest"].pop("algorithmVersion"),
            lambda s: s["declarations"][0].update(canonicalTypeHash=18446744073709551615),
            lambda s: s["declarations"][0].update(provenance={"method": "metadata_proxy_v1"}),
            lambda s: s["declarations"][0]["typeFingerprint"].pop("shapeHash"),
        ]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                packet = self.dna()
                mutate(packet["snapshots"][0])
                with self.assertRaises(ValueError):
                    self.export(dna_path=self.write_packet(packet))

    def test_multiple_generations_for_one_revision_are_not_silently_overwritten(self):
        packet = self.dna()
        duplicate = json.loads(json.dumps(packet["snapshots"][0]))
        duplicate["generation"] = "another-generation"
        packet["snapshots"].append(duplicate)
        with self.assertRaises(ValueError):
            self.export(dna_path=self.write_packet(packet))

    def test_acyclicity_is_checked_independently_of_time(self):
        with self.assertRaises(ValueError):
            exporter.topological({"a": {"parents": ["b"]}, "b": {"parents": ["a"]}})


if __name__ == "__main__":
    unittest.main()
