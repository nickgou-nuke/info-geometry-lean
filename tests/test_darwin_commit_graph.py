from __future__ import annotations

import subprocess

from tools.infra import darwin_commit_graph
from tools.infra.darwin_evolution_algorithms import change_facet_summary
from tools.infra.darwin_commit_graph import iter_parent_edges


def test_parent_edges_point_from_each_parent_to_child_and_keep_slot() -> None:
    commits = [
        {"_key": "root"},
        {"_key": "left", "parents": ["root"]},
        {"_key": "merge", "parents": ["left", "root"]},
    ]

    edges = list(iter_parent_edges(commits, {row["_key"] for row in commits}))

    assert edges == [
        {
            "_key": "root__left__p0",
            "_from": "commit_nodes/root",
            "_to": "commit_nodes/left",
            "edgeKind": "parent_of",
            "parent_slot": 0,
        },
        {
            "_key": "left__merge__p0",
            "_from": "commit_nodes/left",
            "_to": "commit_nodes/merge",
            "edgeKind": "parent_of",
            "parent_slot": 0,
        },
        {
            "_key": "root__merge__p1",
            "_from": "commit_nodes/root",
            "_to": "commit_nodes/merge",
            "edgeKind": "parent_of",
            "parent_slot": 1,
        },
    ]


def test_missing_shallow_boundary_parent_is_not_emitted_as_edge() -> None:
    commits = [{"_key": "child", "parents": ["external-parent"]}]

    assert list(iter_parent_edges(commits, {"child"})) == []


def test_change_facet_summary_counts_categories_without_rank_transitions() -> None:
    label = {
        "category": "Bug Fix",
        "categoryId": "bugFix",
        "ruleWeightPercent": 85,
        "evidenceKinds": ["subjectBodyRule"],
        "status": "weak_rule",
    }

    class Collection:
        def all(self):
            return iter([
                {"_key": "a", "changeLabels": [label]},
                {"_key": "b", "changeLabels": [label], "taxonRank": "Species"},
                {"_key": "c", "changeLabels": [{"category": "malformed"}]},
            ])

    class Database:
        def collection(self, name):
            assert name == "commit_nodes"
            return Collection()

    summary = change_facet_summary(Database())

    assert summary["hierarchical"] is False
    assert summary["method"] == "weak-rule-v3"
    assert summary["commits"] == 3
    assert summary["labeledCommits"] == 2
    assert summary["malformedLabelCount"] == 1
    assert summary["legacyRankRecordCount"] == 1
    assert summary["categories"] == [{
        "category": "Bug Fix",
        "categoryId": "bugFix",
        "commits": 2,
        "ruleWeightsAreProbabilities": False,
    }]


def test_changed_paths_reads_root_and_merge_path_metadata_only(tmp_path, monkeypatch) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()

    def git(*args: str) -> str:
        return subprocess.check_output(
            ["git", *args], cwd=repo, text=True, stderr=subprocess.PIPE
        ).strip()

    git("init", "-q", "-b", "main")
    git("config", "user.name", "Test")
    git("config", "user.email", "test@example.invalid")
    (repo / "root.txt").write_text("root\n")
    git("add", "root.txt")
    git("commit", "-q", "-m", "root")
    root = git("rev-parse", "HEAD")

    git("switch", "-q", "-c", "feature")
    (repo / "feature.txt").write_text("feature\n")
    git("add", "feature.txt")
    git("commit", "-q", "-m", "feature")
    git("switch", "-q", "main")
    (repo / "main.txt").write_text("main\n")
    git("add", "main.txt")
    git("commit", "-q", "-m", "main change")
    git("merge", "-q", "--no-ff", "feature", "-m", "merge")
    merge = git("rev-parse", "HEAD")

    monkeypatch.setattr(darwin_commit_graph, "REPO_ROOT", repo)
    _, root_paths = darwin_commit_graph._changed_paths(root)
    _, merge_paths = darwin_commit_graph._changed_paths(merge)

    assert root_paths == ["root.txt"]
    assert set(merge_paths) == {"feature.txt", "main.txt"}
