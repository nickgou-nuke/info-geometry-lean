"""The batch InfoTree exporter delegates Lean runs through the shared lock."""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import ANY, patch

import pytest

from tools.infra import batch_raw_infotree_export as batch
from tools.infra.pantograph_environment import build_lean_context_manifest


@pytest.mark.parametrize("python_executable", sorted({sys.executable, "/usr/bin/python3"}))
def test_documented_batch_and_validator_script_paths_load_repo_package(python_executable):
    if not Path(python_executable).exists():
        pytest.skip("system Python is unavailable on this platform")
    repository_root = Path(__file__).resolve().parents[1]
    for relative_script in (
        "tools/infra/batch_raw_infotree_export.py",
        "tools/infra/validate_raw_infotree_export.py",
    ):
        result = subprocess.run(
            [python_executable, str(repository_root / relative_script), "--help"],
            cwd=repository_root,
            check=False,
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, f"{relative_script}: {result.stderr}"


def test_export_one_uses_locked_lean_script_runner():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        source = root / "lean" / "Sample.lean"
        source.parent.mkdir()
        source.write_text("def sample := 1\n", encoding="utf-8")
        script = root / "lean" / "DAG" / "RawInfoTreeExport.lean"
        script.parent.mkdir()
        script.write_text("def main := pure ()\n", encoding="utf-8")
        output = root / "out" / "sample"

        with (
            patch.object(batch, "ROOT", root),
            patch.object(batch, "EXPORTER", script),
            patch.object(batch, "execute_locked_lean", return_value=subprocess.CompletedProcess([], 0, "", "")) as run,
            patch.object(batch, "validate_export", return_value=(0, {"ok": True}, "", "")),
        ):
            result = batch.export_one(source, output, 17, "/opt/lean/bin/lake", require_olean=False)

    assert result.status == "ok"
    run.assert_called_once_with(
        Path("lean/DAG/RawInfoTreeExport.lean"),
        [str(Path("lean/Sample.lean")), str(Path("out/sample"))],
        lake="/opt/lean/bin/lake",
        root=root,
        run_script=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=ANY,
        timeout=17,
    )


def test_timeout_preserves_live_diagnostic_log_and_bounded_report_tail(tmp_path):
    source = tmp_path / "Sample.lean"
    source.write_text("def sample := 1\n")
    output = tmp_path / "capture"
    diagnostic = b"x" * 40000 + b"\nphase=walk_root index=12\n"

    def execute(*args, **kwargs):
        kwargs["stderr"].write(diagnostic)
        kwargs["stderr"].flush()
        assert (output / "export.stderr.log").read_bytes() == diagnostic
        raise subprocess.TimeoutExpired(["lake"], 1, output=b"partial")

    with patch.object(batch, "execute_locked_lean", side_effect=execute):
        result = batch.export_one(source, output, 1, "lake", require_olean=False)
    assert result.status == "timeout"
    assert result.stderr_tail.endswith("phase=walk_root index=12\n")
    assert len(result.stderr_tail) <= 8000
    assert (output / "export.stderr.log").read_bytes() == diagnostic
    assert result.source_provenance is None


def test_export_one_preserves_existing_capture_directory(tmp_path: Path):
    source = tmp_path / "Sample.lean"
    source.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
    output = tmp_path / "capture"
    output.mkdir()
    marker = output / "raw_infotree_nodes.jsonl"
    marker.write_text('{"existing":true}\n', encoding="utf-8")

    with patch.object(batch, "ROOT", tmp_path):
        result = batch.export_one(source, output, 5, "lake", require_olean=False)

    assert result.status == "output_exists"
    assert marker.read_text(encoding="utf-8") == '{"existing":true}\n'


def test_timeout_diagnostics_survive_batch_report_serialization(tmp_path: Path):
    source = tmp_path / "Sample.lean"
    source.write_text("def sample := 1\n")
    args = batch.argparse.Namespace(
        output_dir=tmp_path / "capture", resume=False, merge=False,
        no_merge=False, timeout_sec=1, lake="lake", allow_missing_olean=True,
        allow_failures=False,
    )
    timeout = subprocess.TimeoutExpired(
        ["lake"], 1, output=b"partial output\xff", stderr=b"diagnostic\n"
    )
    with (
        patch.object(batch, "ROOT", tmp_path),
        patch.object(batch, "EXPORTER", tmp_path / "Exporter.lean"),
        patch.object(batch, "parse_args", return_value=args),
        patch.object(batch, "discover_files", return_value=[source]),
        patch.object(batch, "execute_locked_lean", side_effect=timeout),
    ):
        assert batch.main() == 2
    report = json.loads((args.output_dir / "batch_report.json").read_text())
    assert report["failure_count"] == 1
    assert report["valid_file_count"] == 0
    assert report["results"][0]["status"] == "timeout"
    assert report["results"][0]["stdout_tail"] == "partial output\ufffd"
    assert report["results"][0]["stderr_tail"] == "diagnostic\n"


@pytest.mark.parametrize("exporter_receipt", ["current", "stale", "missing"])
def test_export_one_resume_reuses_only_bound_validated_capture(tmp_path: Path, exporter_receipt):
    source = tmp_path / "lean" / "Sample.lean"
    source.parent.mkdir()
    source.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
    source_sha = batch.hashlib.sha256(source.read_bytes()).hexdigest()
    context = {
        "sourcePath": "lean/Sample.lean", "sourceSha256": source_sha,
        "fingerprint": "context-fingerprint-v1",
    }
    olean = tmp_path / ".lake/build/lib/lean/Sample.olean"
    olean.parent.mkdir(parents=True)
    olean.write_bytes(b"cached olean")
    output = tmp_path / "capture"
    output.mkdir()
    for filename in batch.JSONL_FILES:
        (output / filename).write_text("", encoding="utf-8")
    provenance = {
        "sourcePath": context["sourcePath"], "sourceSha256": source_sha,
        "leanContextFingerprint": context["fingerprint"],
    }
    provenance["rawCaptureSha256"] = batch._capture_bundle_sha256(output)
    if exporter_receipt != "missing":
        provenance["exporterSourceSha256"] = (
            batch.hashlib.sha256(batch.EXPORTER.read_bytes()).hexdigest()
            if exporter_receipt == "current" else "0" * 64
        )
    (output / "metadata.json").write_text(
        json.dumps({"sourceProvenance": provenance}), encoding="utf-8"
    )

    with (
        patch.object(batch, "ROOT", tmp_path),
        patch.object(batch, "build_lean_context_manifest", return_value=context),
        patch.object(batch, "validate_export", return_value=(0, {"ok": True}, "", "")),
        patch.object(batch, "execute_locked_lean") as execute,
    ):
        result = batch.export_one(
            source, output, 5, "lake", require_olean=True, resume=True,
        )

    assert result.status == ("reused" if exporter_receipt == "current"
                             else "resume_unverified_existing")
    if exporter_receipt != "current":
        assert "exporter source receipt" in result.stderr_tail
    execute.assert_not_called()


def test_resume_refuses_changed_capture_rows_without_replacing_them(tmp_path: Path):
    source = tmp_path / "lean" / "Sample.lean"
    source.parent.mkdir()
    source.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
    source_sha = batch.hashlib.sha256(source.read_bytes()).hexdigest()
    context = {
        "sourcePath": "lean/Sample.lean", "sourceSha256": source_sha,
        "fingerprint": "context-fingerprint-v1",
    }
    olean = tmp_path / ".lake/build/lib/lean/Sample.olean"
    olean.parent.mkdir(parents=True)
    olean.write_bytes(b"cached olean")
    output = tmp_path / "capture"
    output.mkdir()
    for filename in batch.JSONL_FILES:
        (output / filename).write_text("", encoding="utf-8")
    provenance = {
        "sourcePath": context["sourcePath"], "sourceSha256": source_sha,
        "leanContextFingerprint": context["fingerprint"],
        "rawCaptureSha256": batch._capture_bundle_sha256(output),
        "exporterSourceSha256": batch.hashlib.sha256(batch.EXPORTER.read_bytes()).hexdigest(),
    }
    (output / "metadata.json").write_text(
        json.dumps({"sourceProvenance": provenance}), encoding="utf-8"
    )
    changed_rows = output / batch.JSONL_FILES[0]
    changed_rows.write_text('{"tampered":true}\n', encoding="utf-8")

    with (
        patch.object(batch, "ROOT", tmp_path),
        patch.object(batch, "build_lean_context_manifest", return_value=context),
        patch.object(batch, "validate_export", return_value=(0, {"ok": True}, "", "")),
        patch.object(batch, "execute_locked_lean") as execute,
    ):
        result = batch.export_one(
            source, output, 5, "lake", require_olean=True, resume=True,
        )

    assert result.status == "resume_unverified_existing"
    assert changed_rows.read_text(encoding="utf-8") == '{"tampered":true}\n'
    execute.assert_not_called()


@pytest.mark.parametrize("change_exporter", [False, True])
def test_capture_binds_exporter_source_and_rejects_midrun_changes(tmp_path: Path, change_exporter):
    source = tmp_path / "Sample.lean"
    source.write_text("def sample := 1\n")
    exporter = tmp_path / "Exporter.lean"
    exporter.write_text("-- original exporter\n")
    original_sha = batch.hashlib.sha256(exporter.read_bytes()).hexdigest()
    context = {"sourcePath": "Sample.lean", "fingerprint": "context",
               "sourceSha256": batch.hashlib.sha256(source.read_bytes()).hexdigest()}
    output = tmp_path / "capture"
    def execute(*args, **kwargs):
        for filename in batch.JSONL_FILES:
            (output / filename).write_text("")
        (output / "metadata.json").write_text("{}")
        if change_exporter:
            exporter.write_text("-- changed exporter\n")
        return subprocess.CompletedProcess([], 0, "", "")
    with (
        patch.object(batch, "ROOT", tmp_path),
        patch.object(batch, "EXPORTER", exporter),
        patch.object(batch, "olean_path_for", return_value=source),
        patch.object(batch, "build_lean_context_manifest", return_value=context),
        patch.object(batch, "execute_locked_lean", side_effect=execute),
        patch.object(batch, "validate_export", return_value=(0, {"ok": True}, "", "")),
    ):
        result = batch.export_one(source, output, 5, "lake", require_olean=True)
    metadata = json.loads((output / "metadata.json").read_text())
    assert result.status == ("exporter_changed" if change_exporter else "ok")
    if change_exporter:
        assert result.source_provenance is None
        assert "sourceProvenance" not in metadata
    else:
        assert metadata["sourceProvenance"]["exporterSourceSha256"] == original_sha


def test_merge_refuses_to_replace_existing_capture_copy(tmp_path: Path):
    merged = tmp_path / "merged"
    merged.mkdir()
    marker = merged / "raw_infotree_nodes.jsonl"
    marker.write_text('{"existing":true}\n', encoding="utf-8")

    with pytest.raises(FileExistsError, match="refusing to replace"):
        batch.merge_valid_exports([], merged)

    assert marker.read_text(encoding="utf-8") == '{"existing":true}\n'


def test_main_fails_before_running_jobs_when_any_capture_path_exists(tmp_path: Path):
    root = tmp_path / "repo"
    source = root / "lean" / "Sample.lean"
    source.parent.mkdir(parents=True)
    source.write_text("theorem sample : True := True.intro\n", encoding="utf-8")
    output = tmp_path / "run"
    existing = output / "per_file" / "00000_lean_Sample.lean"
    existing.mkdir(parents=True)
    marker = existing / "raw_infotree_nodes.jsonl"
    marker.write_text('{"existing":true}\n', encoding="utf-8")
    args = batch.argparse.Namespace(
        files=[], file_list=None, roots=[], limit=None, output_dir=output,
        merge=False, no_merge=False, resume=False,
    )

    with (
        patch.object(batch, "ROOT", root),
        patch.object(batch, "parse_args", return_value=args),
        patch.object(batch, "discover_files", return_value=[source]),
        patch.object(batch, "export_one") as export_one,
    ):
        result = batch.main()

    assert result == 2
    export_one.assert_not_called()
    assert marker.read_text(encoding="utf-8") == '{"existing":true}\n'
    assert not (output / "batch_report.json").exists()


def test_discovery_and_olean_mapping_preserve_lexical_symlink_path():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        target = root / "external/Target.lean"
        target.parent.mkdir(parents=True)
        target.write_text("theorem target : True := True.intro\n")
        alias = root / "lean/TargetAlias.lean"
        alias.parent.mkdir(parents=True)
        try:
            alias.symlink_to("../external/Target.lean")
        except OSError as exc:
            import pytest
            pytest.skip(f"symlink creation unavailable: {exc}")

        args = batch.argparse.Namespace(
            files=[Path("lean/TargetAlias.lean")], file_list=None, roots=[], limit=None,
        )
        with patch.object(batch, "ROOT", root):
            discovered = batch.discover_files(args)
            olean = batch.olean_path_for(discovered[0])

    assert discovered == [alias.absolute()]
    assert olean == root / ".lake/build/lib/lean/TargetAlias.olean"


def test_lean_context_manifest_fingerprints_alias_module_and_olean(tmp_path: Path):
    target = tmp_path / "external/Target.lean"
    target.parent.mkdir(parents=True)
    target.write_text("theorem target : True := True.intro\n")
    alias = tmp_path / "lean/TargetAlias.lean"
    alias.parent.mkdir(parents=True)
    try:
        alias.symlink_to("../external/Target.lean")
    except OSError as exc:
        import pytest
        pytest.skip(f"symlink creation unavailable: {exc}")
    for filename, content in (("lean-toolchain", "leanprover/lean4:v4.34.1\n"),
                              ("lakefile.lean", "package sample\n"),
                              ("lake-manifest.json", "{}\n")):
        (tmp_path / filename).write_text(content)
    target_olean = tmp_path / ".lake/build/lib/lean/TargetAlias.olean"
    target_olean.parent.mkdir(parents=True)
    target_olean.write_bytes(b"alias olean")
    dependency_olean = tmp_path / ".lake/build/lib/lean/Dependency.olean"
    dependency_olean.write_bytes(b"dependency olean")

    def runner(args, **kwargs):
        if args[-2:] == ["lean", "--deps"] or (len(args) >= 4 and args[-3] == "lean" and args[-2] == "--deps"):
            return subprocess.CompletedProcess(args, 0, f"{dependency_olean}\n", "")
        if args[-2:] == ["lean", "--print-libdir"]:
            return subprocess.CompletedProcess(args, 0, str(tmp_path / "leanlib"), "")
        if args[-2:] == ["lean", "--version"]:
            return subprocess.CompletedProcess(args, 0, "Lean version test", "")
        if args[-2:] == ["lake", "--version"]:
            return subprocess.CompletedProcess(args, 0, "Lake version test", "")
        raise AssertionError(args)

    manifest = build_lean_context_manifest(tmp_path, alias, runner=runner)

    assert manifest["sourcePath"] == "lean/TargetAlias.lean"
    assert manifest["sourceSha256"]
    assert "project:.lake/build/lib/lean/TargetAlias.olean" in {
        row["path"] for row in manifest["sourceLeanOleans"]
    }
