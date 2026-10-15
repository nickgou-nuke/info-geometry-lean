"""Safety regressions use mocked compilers/providers/DB calls only."""
import json
import subprocess
from types import SimpleNamespace

import pytest

from igf.common.json_io import load_strict_jsonl
from igf.graph import arango_http
from igf.cpg.dedup import ArangoCPGDeduplicator
from tools import check_vacuity_policy
from tools.infra import decl_graph_support
from tools.infra.vacuity_critic import VacuityCritic, FailCase
from tools.leantrail import vacuity_audit


def test_cursor_fetches_all_pages(monkeypatch):
    pages = iter([{"result": [1], "hasMore": True, "id": "cursor"},
                  {"result": [2, 3], "hasMore": False}])
    calls = []
    def request(*args, **kwargs):
        calls.append(args[0])
        return next(pages)
    monkeypatch.setattr(arango_http, "request_json", request)
    target = arango_http.ArangoHttpTarget("http://localhost", "db", "user", "")
    assert arango_http.execute_aql(target, "RETURN 1") == [1, 2, 3]
    assert calls == ["POST", "PUT"]


@pytest.mark.parametrize("page", [
    {"result": [], "hasMore": True},
    {"result": [], "hasMore": False, "error": True},
    {"result": [], "hasMore": False, "extra": {"warnings": [{"code": 1}]}},
    {"result": "not rows", "hasMore": False},
])
def test_incomplete_cursor_never_returns_success(monkeypatch, page):
    monkeypatch.setattr(arango_http, "request_json", lambda *a, **kw: page)
    target = arango_http.ArangoHttpTarget("http://localhost", "db", "user", "")
    with pytest.raises(RuntimeError):
        arango_http.execute_aql(target, "RETURN 1")


@pytest.mark.parametrize("content", ['{"name":"a"}\nbroken\n', '{"name":NaN}\n', '[]\n'])
def test_bad_jsonl_is_not_silently_skipped(tmp_path, content):
    path = tmp_path / "rows.jsonl"
    path.write_text(content)
    with pytest.raises(ValueError):
        load_strict_jsonl(path, ("name",))


def test_cpg_thresholds_reach_every_query(tmp_path):
    client = object.__new__(ArangoCPGDeduplicator)
    calls = []
    def query(sql, bindings):
        calls.append((sql, bindings))
        return []
    client._query = query
    report = client.generate_deduplication_manifest(tmp_path / "dedup.json", min_count=7, limit=11)
    assert len(calls) == 3
    for sql, bindings in calls:
        assert bindings == {"min_count": 7, "limit": 11}
        assert "IS_STRING" in sql and "@min_count" in sql and "@limit" in sql
    assert report["parameters"] == {"min_count": 7, "limit": 11}


@pytest.mark.parametrize("entries", [[], [{"name": "A", "file": "A.lean"}],
    [{"name": "A", "file": "A.lean", "violations": [], "semantic_audit_performed": False}],
    [{"name": "A", "file": "A.lean", "violations": [{"level": "bogus", "code": "x"}]}]])
def test_missing_policy_evidence_cannot_pass(tmp_path, entries):
    report = tmp_path / "report.json"
    report.write_text(json.dumps(entries))
    assert check_vacuity_policy.check_policy(report, strict_paths=[], bridge_hints=[], verbose=False) == 2


def test_dry_run_calls_no_provider_and_writes_no_schema(tmp_path, monkeypatch):
    schema = tmp_path / "schema.json"
    critic = VacuityCritic(schema_path=schema, dry_run=True)
    def forbidden(*a, **kw):
        raise AssertionError("provider or mutation during dry run")
    monkeypatch.setattr(critic, "_classify_pattern", forbidden)
    monkeypatch.setattr(critic, "_load_hermes_env", forbidden)
    monkeypatch.setattr(critic, "_extract_field_name", lambda _: "foo_newsuffix")
    monkeypatch.setattr(critic, "_extract_suffix", lambda _: "_newsuffix")
    monkeypatch.setattr(critic, "_is_known_pattern", lambda _: False)
    pattern = SimpleNamespace(name="new", category="review")
    monkeypatch.setattr(critic, "_heuristic_classify", lambda *a: pattern)
    count = len(critic._patterns)
    failure = FailCase("A.lean", 1, "skill", "", "", "", "foo_newsuffix : True", "")
    assert critic.review_failures([failure]) == [pattern]
    assert len(critic._patterns) == count
    assert critic.synthesize_candidates() == []
    critic._save_schema()
    assert not schema.exists()


def test_graph_read_does_not_refresh_or_query(tmp_path, monkeypatch):
    def forbidden(*a, **kw):
        raise AssertionError("graph read triggered refresh or DB query")
    monkeypatch.setattr(decl_graph_support, "get_authority_data", forbidden)
    monkeypatch.setattr(decl_graph_support, "ensure_truth_artifacts", forbidden)
    with pytest.raises(FileNotFoundError):
        decl_graph_support.load_decl_graph(tmp_path)


def test_biopsy_observation_timeout_does_not_kill(monkeypatch):
    events = []
    class Lock:
        def fileno(self): return 17
        def release(self): events.append("release")
    class Process:
        pid = 99999999
        returncode = None
        def __init__(self, argv, **kwargs):
            assert kwargs["pass_fds"] == (17,)
            self.output = kwargs["stdout"]
            self.calls = 0
        def wait(self, timeout=None):
            self.calls += 1
            events.append("wait")
            if self.calls == 1:
                raise subprocess.TimeoutExpired("fake-compiler", timeout)
            self.output.write(b'Owner.lean:1:0: info: {"target":"Owner.a"}\n')
            self.returncode = 0
            return 0
        def poll(self): return self.returncode
        def kill(self): raise AssertionError("compiler killed")
        def terminate(self): raise AssertionError("compiler terminated")
    monkeypatch.setattr(vacuity_audit, "acquire_build_lock", lambda *a, **kw: Lock())
    monkeypatch.setattr(vacuity_audit.subprocess, "run", lambda *a, **kw: SimpleNamespace(returncode=1))
    monkeypatch.setattr(vacuity_audit.subprocess, "Popen", Process)
    monkeypatch.setattr(vacuity_audit, "process_group_has_live_members", lambda _: False)
    rc, output = vacuity_audit.run_lean_script("-- synthetic input", timeout=1)
    assert rc == 0 and events == ["wait", "wait", "release"]
    assert vacuity_audit.parse_biopsy_json(output) == [{"target": "Owner.a"}]


def test_biopsy_matches_targets_and_rejects_debt(tmp_path, monkeypatch):
    snapshot = tmp_path / "snapshot.json"
    snapshot.write_text(json.dumps({"nodes": [{"kind": "Declaration", "name": "Owner.a", "module": "Owner"}]}))
    row = {"target": "Owner.a", "attrs": {"vacuity": {"role": "closure_debt"},
           "contamination": {"state": "honest_sorry"}}}
    monkeypatch.setattr(vacuity_audit, "run_lean_script", lambda *a, **kw: (0, json.dumps(row)))
    report = vacuity_audit.run(snapshot_path=snapshot, out_path=tmp_path / "rows.jsonl",
        json_out=tmp_path / "report.json", module_prefix=None, decl_prefix=None,
        decls=[], limit=None, module_batch_size=25, timeout=1, keep_going=True)
    assert report["execution_ok"] and not report["ok"]
    assert report["semantic_clearance"] is False
    assert report["unresolved_finding_count"] == 1
    emitted = json.loads((tmp_path / "rows.jsonl").read_text())
    assert emitted["run_id"] == report["run_id"]
