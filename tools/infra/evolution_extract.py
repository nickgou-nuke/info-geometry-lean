#!/usr/bin/env python3
"""One-pass, resumable Git history extraction to JSONL.

The commit graph is the deduplicated union reachable from ``--all`` refs.
Metadata, body, trailers and shortstat share one ``git log`` traversal. Output
is checkpointed to disk; memory is bounded by a commit record and one small
checkpoint batch. File-level change paths belong to the separate optional
stream because shortstat does not contain rename/copy or co-change data.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import sqlite3
import subprocess
import sys
from pathlib import Path
from typing import Iterator

FIELD_SEP = b"\x1f"
RECORD_SEP = b"\x1e"
BODY_SEP = b"\x1d"
RECORD_MARKER = RECORD_SEP + b"COMMIT" + FIELD_SEP
SHORTSTAT = re.compile(
    r"(?m)^\s*(\d+) files? changed"
    r"(?:,\s*(\d+) insertions?\(\+\))?"
    r"(?:,\s*(\d+) deletions?\(-\))?\s*$"
)
TRAILER = re.compile(r"^([A-Za-z0-9][A-Za-z0-9-]*):[ \t]*(.*)$")


def _ref_fingerprint(repo: Path) -> str:
    refs = subprocess.check_output(
        ["git", "for-each-ref", "--format=%(refname) %(objectname)"], cwd=repo
    )
    head_result = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"], cwd=repo,
        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, check=False,
    )
    head = head_result.stdout if head_result.returncode == 0 else b""
    return hashlib.sha256(refs + b"\0HEAD\0" + head).hexdigest()


def _git_records(repo: Path, stderr_path: Path) -> Iterator[bytes]:
    """Yield commit records using fixed-size reads from one git-log process.

    Git's pretty-format framing is checked structurally before a record is
    accepted. The reserved control-byte marker is interpreted only when
    followed by the complete metadata header shape and a valid object ID.
    """
    pretty = (
        "--pretty=format:%x1eCOMMIT%x1f%H%x1f%P%x1f%an%x1f%ae%x1f%at%x1f%ad"
        "%x1f%cn%x1f%ce%x1f%ct%x1f%cd%x1f%s%x1d%b"
    )
    with stderr_path.open("ab") as errlog:
        proc = subprocess.Popen(
            ["git", "log", "--all", "--date=iso-strict", "--shortstat", pretty],
            cwd=repo, stdout=subprocess.PIPE, stderr=errlog, bufsize=1024 * 64,
        )
        yield from _read_git_records(proc)


def _read_git_records(proc: subprocess.Popen) -> Iterator[bytes]:
    assert proc.stdout is not None
    pending = bytearray()
    current: bytearray | None = None
    try:
        while chunk := proc.stdout.read(64 * 1024):
            pending.extend(chunk)
            while True:
                pos = pending.find(RECORD_MARKER)
                if pos < 0:
                    if current is not None and len(pending) > len(RECORD_MARKER):
                        keep = len(RECORD_MARKER) - 1
                        current.extend(pending[:-keep])
                        del pending[:-keep]
                    break
                candidate = pending[pos + len(RECORD_MARKER):]
                sha_end = candidate.find(FIELD_SEP)
                if sha_end < 0 and len(candidate) < 65:
                    # The marker may straddle a fixed-size read boundary. Keep
                    # it intact until its complete object ID and separator arrive.
                    if pos:
                        if current is not None:
                            current.extend(pending[:pos])
                        del pending[:pos]
                    break
                sha = candidate[:sha_end] if sha_end >= 0 else candidate
                if len(sha) not in (40, 64) or not re.fullmatch(rb"[0-9a-f]+", sha):
                    if current is None:
                        del pending[:pos + 1]
                    else:
                        current.extend(pending[:pos + 1])
                        del pending[:pos + 1]
                    continue
                if current is not None:
                    current.extend(pending[:pos])
                    yield bytes(current)
                del pending[:pos + len(RECORD_MARKER)]
                current = bytearray(b"COMMIT" + FIELD_SEP + pending[:len(sha)])
                del pending[:len(sha)]
        if current is not None:
            current.extend(pending)
            yield bytes(current)
    except BaseException:
        proc.stdout.close()
        proc.wait()
        raise
    else:
        proc.stdout.close()
    code = proc.wait()
    if code:
        raise subprocess.CalledProcessError(code, proc.args)


def _trailers(body: str) -> list[dict[str, str]]:
    """Extract a final trailer block, retaining duplicate keys and order."""
    lines = body.rstrip().splitlines()
    parsed: list[dict[str, str]] = []
    for line in reversed(lines):
        match = TRAILER.match(line)
        if match:
            parsed.append({"key": match.group(1), "value": match.group(2)})
        elif line.startswith((" ", "\t")) and parsed:
            parsed[-1]["value"] = line.strip() + "\n" + parsed[-1]["value"]
        elif not line and parsed:
            break
        else:
            return []
    return list(reversed(parsed))


def _parse_record(raw: bytes) -> dict | None:
    header, sep, message_stats = raw.partition(BODY_SEP)
    if not sep:
        return None
    framed_header = header.removeprefix(b"COMMIT")
    if framed_header.startswith(FIELD_SEP):
        framed_header = framed_header[1:]
    fields = framed_header.split(FIELD_SEP, 10)
    if len(fields) != 11:
        return None
    decoded = [part.decode("utf-8", errors="replace") for part in fields]
    (sha, parents_raw, author, author_email, author_ts, authored_at, committer,
     committer_email, commit_ts, committed_at, subject) = decoded
    text = message_stats.decode("utf-8", errors="replace")
    stats = list(SHORTSTAT.finditer(text))
    if stats:
        match = stats[-1]
        body = text[:match.start()].rstrip("\n")
        files, insertions, deletions = match.groups()
    else:
        body, files, insertions, deletions = text.rstrip("\n"), "0", "0", "0"
    parents = parents_raw.split()
    return {
        "type": "commit", "sha": sha, "parents": parents,
        "parent_count": len(parents), "is_merge": len(parents) > 1,
        "history_scope": "union_of_all_refs",
        "author_name": author, "author_email": author_email,
        "authored_timestamp": int(author_ts), "authored_at": authored_at,
        "committer_name": committer, "committer_email": committer_email,
        "committed_timestamp": int(commit_ts), "committed_at": committed_at,
        "subject": subject, "body": body, "trailers": _trailers(body),
        "files_changed": int(files), "insertions": int(insertions or 0),
        "deletions": int(deletions or 0),
    }


def stream_to_jsonl(repo: Path, destination: Path, *, resume: bool = False,
                    checkpoint_every: int = 128) -> int:
    """Checkpoint each bounded batch; ``--resume`` truncates uncommitted tail."""
    partial = destination.with_name(destination.name + ".partial")
    state_path = destination.with_name(destination.name + ".checkpoint.sqlite3")
    stderr_path = destination.with_name(destination.name + ".git.stderr.log")
    fingerprint = _ref_fingerprint(repo)
    if not resume and partial.exists():
        raise FileExistsError("partial/checkpoint exists; pass --resume or move it aside")
    if not resume and state_path.exists():
        state_path.unlink()
    if resume and not state_path.exists():
        raise FileNotFoundError("resume requires the checkpoint database")

    state = sqlite3.connect(state_path)
    state.execute("CREATE TABLE IF NOT EXISTS metadata (key TEXT PRIMARY KEY, value TEXT NOT NULL)")
    state.execute("CREATE TABLE IF NOT EXISTS emitted (sha TEXT PRIMARY KEY)")
    stored = dict(state.execute("SELECT key, value FROM metadata"))
    if stored and stored.get("refs_fingerprint") != fingerprint:
        state.close()
        raise RuntimeError("Git refs changed since checkpoint; start a new extraction")
    state.execute("INSERT OR REPLACE INTO metadata VALUES ('refs_fingerprint', ?)", (fingerprint,))
    state.commit()
    if resume and stored.get("complete") == "1" and destination.exists():
        count = int(state.execute("SELECT COUNT(*) FROM emitted").fetchone()[0])
        state.close()
        return count
    if resume and not partial.exists():
        state.close()
        raise FileNotFoundError("resume requires the partial JSONL")
    offset = int(stored.get("committed_bytes", "0"))
    mode = "r+b" if resume else "w+b"
    emitted_count = int(state.execute("SELECT COUNT(*) FROM emitted").fetchone()[0])
    pending_shas: list[str] = []
    try:
        with partial.open(mode, buffering=0) as out:
            if resume:
                if partial.stat().st_size < offset:
                    raise RuntimeError("partial JSONL is shorter than checkpoint")
                out.truncate(offset)
                out.seek(offset)
            for raw in _git_records(repo, stderr_path):
                record = _parse_record(raw)
                if record is None:
                    raise ValueError("Git record did not match the declared stream format")
                sha = record["sha"]
                if state.execute("SELECT 1 FROM emitted WHERE sha = ?", (sha,)).fetchone():
                    continue
                out.write((json.dumps(record, ensure_ascii=False) + "\n").encode("utf-8"))
                pending_shas.append(sha)
                emitted_count += 1
                if len(pending_shas) >= checkpoint_every:
                    os.fsync(out.fileno())
                    offset = out.tell()
                    with state:
                        state.executemany("INSERT OR IGNORE INTO emitted VALUES (?)",
                                          ((item,) for item in pending_shas))
                        state.execute("INSERT OR REPLACE INTO metadata VALUES ('committed_bytes', ?)",
                                      (str(offset),))
                    pending_shas.clear()
                    print(f"[evolution_extract] checkpointed {emitted_count} commits",
                          file=sys.stderr, flush=True)
            if pending_shas:
                os.fsync(out.fileno())
                offset = out.tell()
                with state:
                    state.executemany("INSERT OR IGNORE INTO emitted VALUES (?)",
                                      ((item,) for item in pending_shas))
                    state.execute("INSERT OR REPLACE INTO metadata VALUES ('committed_bytes', ?)",
                                  (str(offset),))
            out.flush()
            os.fsync(out.fileno())
        if _ref_fingerprint(repo) != fingerprint:
            raise RuntimeError("Git refs changed during extraction; checkpoint retained")
        with state:
            state.execute("INSERT OR REPLACE INTO metadata VALUES ('complete', '1')")
        os.replace(partial, destination)
        state.close()
        return emitted_count
    except BaseException:
        state.close()
        raise


def _nul_tokens(stream) -> Iterator[bytes]:
    """Yield NUL-delimited Git path/status fields with fixed-size reads."""
    pending = bytearray()
    while chunk := stream.read(64 * 1024):
        pending.extend(chunk)
        start = 0
        while (end := pending.find(b"\0", start)) >= 0:
            yield bytes(pending[start:end])
            start = end + 1
        if start:
            del pending[:start]
    if pending:
        yield bytes(pending)


def _path_fields(raw: bytes, prefix: str) -> dict[str, str]:
    """Keep readable UTF-8 paths compact; preserve raw bytes only when needed."""
    try:
        return {prefix: raw.decode("utf-8")}
    except UnicodeDecodeError:
        return {prefix: raw.decode("utf-8", errors="replace"),
                prefix + "_base64": base64.b64encode(raw).decode("ascii")}


def _write_file_stream(repo: Path, destination: Path, *, numstat: bool,
                       resume: bool = False, checkpoint_every: int = 128,
                       find_copies: bool = False,
                       path_prefixes: tuple[str, ...] = ()) -> int:
    """Stream one file-level view to JSONL with commit-boundary checkpoints."""
    partial = destination.with_name(destination.name + ".partial")
    state_path = destination.with_name(destination.name + ".checkpoint.sqlite3")
    refs_fingerprint = _ref_fingerprint(repo)
    fingerprint = hashlib.sha256(
        f"{refs_fingerprint}:{'numstat' if numstat else 'name-status'}:"
        f"find_copies={find_copies}:paths={path_prefixes!r}".encode()
    ).hexdigest()
    if not resume and partial.exists():
        raise FileExistsError("partial/checkpoint exists; pass --resume or move it aside")
    if not resume and state_path.exists():
        state_path.unlink()
    if resume and not state_path.exists():
        raise FileNotFoundError("resume requires the checkpoint database")
    state = sqlite3.connect(state_path)
    state.execute("CREATE TABLE IF NOT EXISTS metadata (key TEXT PRIMARY KEY, value TEXT NOT NULL)")
    state.execute("CREATE TABLE IF NOT EXISTS completed (sha TEXT PRIMARY KEY)")
    stored = dict(state.execute("SELECT key, value FROM metadata"))
    if stored and stored.get("fingerprint") != fingerprint:
        state.close()
        raise RuntimeError("Git refs or file-stream mode changed since checkpoint")
    state.execute("INSERT OR REPLACE INTO metadata VALUES ('fingerprint', ?)", (fingerprint,))
    state.commit()
    if resume and stored.get("complete") == "1" and destination.exists():
        count = int(stored.get("row_count", "0"))
        state.close()
        return count
    if resume and not partial.exists():
        state.close()
        raise FileNotFoundError("resume requires the partial JSONL")
    offset = int(stored.get("committed_bytes", "0"))
    total = int(stored.get("row_count", "0"))
    pending_shas: list[str] = []
    args = ["git", "log", "--all", "--find-renames", "--find-copies", "-z"]
    if not find_copies:
        args.remove("--find-copies")
    if numstat:
        args.append("--numstat")
        fmt = "--format=COMMIT%x00%H%x00%P%x00"
    else:
        args.extend(["--name-status"])
        fmt = "--format=COMMIT%x00%H%x00%P%x00"
    args.append(fmt)
    if path_prefixes:
        args.extend(["--", *path_prefixes])
    stderr_path = destination.with_name(destination.name + ".git.stderr.log")
    errlog = stderr_path.open("ab")
    proc = subprocess.Popen(args, cwd=repo, stdout=subprocess.PIPE, stderr=errlog)
    assert proc.stdout is not None
    count = total
    current_sha: str | None = None
    skip_current = False
    tokens = iter(_nul_tokens(proc.stdout))
    try:
        with partial.open("r+b" if resume else "w+b", buffering=0) as out:
            if resume:
                if partial.stat().st_size < offset:
                    raise RuntimeError("partial JSONL is shorter than checkpoint")
                out.truncate(offset)
                out.seek(offset)

            def checkpoint() -> None:
                nonlocal offset, pending_shas
                if not pending_shas:
                    return
                os.fsync(out.fileno())
                offset = out.tell()
                with state:
                    state.executemany("INSERT OR IGNORE INTO completed VALUES (?)",
                                      ((sha,) for sha in pending_shas))
                    state.execute("INSERT OR REPLACE INTO metadata VALUES ('committed_bytes', ?)",
                                  (str(offset),))
                    state.execute("INSERT OR REPLACE INTO metadata VALUES ('row_count', ?)",
                                  (str(count),))
                print(f"[evolution_extract] checkpointed {len(pending_shas)} commits, "
                      f"{count} file rows", file=sys.stderr, flush=True)
                pending_shas = []

            for token in tokens:
                if token.startswith(b"\n"):
                    token = token[1:]
                if token == b"COMMIT":
                    if current_sha is not None and not skip_current:
                        pending_shas.append(current_sha)
                        if len(pending_shas) >= checkpoint_every:
                            checkpoint()
                    current_sha = next(tokens).decode("ascii")
                    next(tokens)  # parents are already recorded on the commit vertex
                    skip_current = state.execute(
                        "SELECT 1 FROM completed WHERE sha = ?", (current_sha,)
                    ).fetchone() is not None
                    continue
                if current_sha is None or skip_current:
                    continue
                if not token:
                    continue
                if numstat:
                    fields = token.split(b"\t", 2)
                    if len(fields) != 3:
                        raise ValueError(f"malformed numstat token: {token!r}")
                    added, deleted, path = fields
                    row = {"type": "file_numstat", "sha": current_sha,
                           "additions": None if added == b"-" else int(added),
                           "deletions": None if deleted == b"-" else int(deleted)}
                    if path:
                        row.update(_path_fields(path, "path"))
                    else:
                        old_path, new_path = next(tokens), next(tokens)
                        row["change_type"] = "rename_or_copy"
                        row.update(_path_fields(old_path, "old_path"))
                        row.update(_path_fields(new_path, "path"))
                else:
                    if not re.fullmatch(rb"[ACDMRTUXB][0-9]*", token):
                        raise ValueError(f"malformed name-status token: {token!r}")
                    status = token.decode("ascii", errors="replace")
                    row = {"type": "commit_file", "sha": current_sha,
                           "change_type": status[0], "similarity": status[1:] or None}
                    if status.startswith(("R", "C")):
                        old_path, new_path = next(tokens), next(tokens)
                        row.update(_path_fields(old_path, "old_path"))
                        row.update(_path_fields(new_path, "path"))
                    else:
                        row.update(_path_fields(next(tokens), "path"))
                out.write((json.dumps(row, ensure_ascii=True) + "\n").encode("utf-8"))
                count += 1
            if current_sha is not None and not skip_current:
                pending_shas.append(current_sha)
            checkpoint()
            out.flush()
            os.fsync(out.fileno())
        proc.stdout.close()
        code = proc.wait()
        errlog.close()
        if code:
            raise subprocess.CalledProcessError(code, proc.args)
        if _ref_fingerprint(repo) != refs_fingerprint:
            raise RuntimeError("Git refs changed during file extraction; checkpoint retained")
        with state:
            state.execute("INSERT OR REPLACE INTO metadata VALUES ('complete', '1')")
        os.replace(partial, destination)
        state.close()
    except BaseException:
        proc.stdout.close()
        proc.wait()
        errlog.close()
        state.close()
        raise
    return count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, nargs="?",
                        help="commit JSONL output (optional with --details-only)")
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--details-only", action="store_true",
                        help="skip metadata extraction and run only requested file-level streams")
    parser.add_argument("--checkpoint-every", type=int, default=128)
    parser.add_argument("--paths-output", type=Path,
                        help="optional streamed rename/copy-aware commit-file JSONL")
    parser.add_argument("--find-copies", action="store_true",
                        help="enable expensive Git copy detection in the path stream")
    parser.add_argument("--path-prefix", action="append", default=[],
                        help="limit file-detail extraction to a Git path/prefix; repeatable")
    parser.add_argument("--numstat-output", type=Path,
                        help="optional streamed file additions/deletions JSONL")
    args = parser.parse_args()
    if args.checkpoint_every < 1:
        parser.error("--checkpoint-every must be positive")
    if not args.details_only and args.output is None:
        parser.error("output is required unless --details-only is set")
    if args.details_only and not (args.paths_output or args.numstat_output):
        parser.error("--details-only requires --paths-output or --numstat-output")
    repo = args.repo.resolve()
    count = 0
    if args.output is not None:
        destination = args.output.expanduser().resolve()
        destination.parent.mkdir(parents=True, exist_ok=True)
        count = stream_to_jsonl(repo, destination, resume=args.resume,
                                checkpoint_every=args.checkpoint_every)
    if args.paths_output:
        path_count = _write_file_stream(repo, args.paths_output.expanduser().resolve(),
                                        numstat=False, resume=args.resume,
                                        checkpoint_every=args.checkpoint_every,
                                        find_copies=args.find_copies,
                                        path_prefixes=tuple(args.path_prefix))
        print(f"[evolution_extract] streamed {path_count} file-status rows",
              file=sys.stderr, flush=True)
    if args.numstat_output:
        stat_count = _write_file_stream(repo, args.numstat_output.expanduser().resolve(),
                                        numstat=True, resume=args.resume,
                                        checkpoint_every=args.checkpoint_every,
                                        find_copies=args.find_copies,
                                        path_prefixes=tuple(args.path_prefix))
        print(f"[evolution_extract] streamed {stat_count} file-numstat rows",
              file=sys.stderr, flush=True)
    if args.output is not None:
        print(f"[evolution_extract] complete: {count} commits -> {destination}",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
