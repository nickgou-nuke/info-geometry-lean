#!/usr/bin/env python3
"""Read-only Git ancestry export with optional manifest-attested declaration DNA.

UTC window is [since, until). History is collected before filtering, so skewed
commit clocks cannot prune ancestry. No network, database, or Lean build calls.
Fingerprints are navigation evidence; a producer's provenance assertion is not
independently checked against source, oleans, or the Lean kernel by this tool.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import heapq
import json
import os
from pathlib import Path
import re
import subprocess
import sys

SHA = re.compile(r"[0-9a-f]{40}\Z")
DIGEST = re.compile(r"[0-9a-f]{64}\Z")


def git(repo, *args, input=None, check=True):
    env = dict(os.environ, GIT_NO_LAZY_FETCH="1", GIT_TERMINAL_PROMPT="0")
    return subprocess.run(
        ["git", "--no-replace-objects", "-C", str(repo), *args], input=input,
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        env=env, check=check,
    )


def utc(value):
    date = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if date.tzinfo is None:
        date = date.replace(tzinfo=timezone.utc)
    return date.astimezone(timezone.utc)


def iso(value):
    return value.isoformat().replace("+00:00", "Z")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def topological(records):
    """Return oldest-first topology, checking acyclicity without using clocks."""
    children, degree = defaultdict(list), {}
    rank = {sha: i for i, sha in enumerate(records)}
    for sha, row in records.items():
        degree[sha] = sum(parent in records for parent in row["parents"])
        for parent in row["parents"]:
            if parent in records:
                children[parent].append(sha)
    ready = [(rank[sha], sha) for sha in records if not degree[sha]]
    heapq.heapify(ready)
    order = []
    while ready:
        _, sha = heapq.heappop(ready)
        order.append(sha)
        for child in children[sha]:
            degree[child] -= 1
            if degree[child] == 0:
                heapq.heappush(ready, (rank[child], child))
    if len(order) != len(records):
        raise ValueError("commit parent graph contains a cycle")
    return order


def collect_history(repo):
    refs, ignored = [], []
    output = git(repo, "for-each-ref", "--format=%(refname)%00%(objectname)%00%(symref)",
                 "refs/remotes/origin/", "refs/tags/").stdout
    for line in output.splitlines():
        name, sha, symref = line.split("\0")
        if symref or name == "refs/remotes/origin/HEAD":
            continue
        kind = "tag" if name.startswith("refs/tags/") else "branch"
        if kind == "tag":
            peeled = git(repo, "rev-parse", "--verify", name + "^{commit}", check=False)
            if peeled.returncode:
                ignored.append({"name": name, "reason": "does not resolve to a commit"})
                continue
            sha = peeled.stdout.strip()
        if not SHA.fullmatch(sha):
            raise ValueError("this schema requires full SHA-1 commit IDs")
        refs.append({"name": name.removeprefix("refs/remotes/").removeprefix("refs/"),
                     "sha": sha, "kind": kind})
    refs.sort(key=lambda row: (row["name"] != "origin/main", row["kind"], row["name"]))
    if not refs:
        raise ValueError("no origin branch or commit-valued tag refs found")
    tips = list(dict.fromkeys(row["sha"] for row in refs))
    raw = git(repo, "log", "--topo-order", "--no-show-signature", "--no-decorate",
              "--format=%H%x00%P%x00%ct%x00%s", "--stdin", input="\n".join(tips) + "\n").stdout
    records = {}
    for line in reversed(raw.splitlines()):
        sha, parents, timestamp, subject = line.split("\0", 3)
        records[sha] = {"sha": sha, "parents": parents.split(), "time": int(timestamp),
                        "subject": subject, "refs": [], "boundary": False}
    shallow = git(repo, "rev-parse", "--is-shallow-repository").stdout.strip() == "true"
    if shallow:
        # Git log hides shallow-root parents; raw commit headers preserve them.
        for sha, row in records.items():
            if not row["parents"]:
                header = git(repo, "cat-file", "commit", sha).stdout.split("\n\n", 1)[0]
                row["parents"] = [line[7:] for line in header.splitlines() if line.startswith("parent ")]
    for row in refs:
        records[row["sha"]]["refs"].append(row["name"])
    order = topological(records)
    for index, sha in enumerate(order):
        records[sha]["index"] = index
    return records, order, refs, ignored, shallow


def assign_lanes(records, order, main):
    chain, sha = set(), main
    while sha in records and sha not in chain:
        chain.add(sha)
        sha = next(iter(records[sha]["parents"]), None)
    pending = {}
    def free():
        lane = 1
        while lane in pending.values():
            lane += 1
        return lane
    for sha in reversed(order):
        lane = 0 if sha in chain else pending.pop(sha, None)
        if lane is None:
            lane = free()
        records[sha]["lane"] = lane
        for index, parent in enumerate(records[sha]["parents"]):
            if parent not in records or parent in chain or parent in pending:
                continue
            pending[parent] = lane if index == 0 and lane and lane not in pending.values() else free()
    return chain


def load_dna(path, repository, records, included):
    result = {"snapshots": [], "unattached": [], "provenance_validation": "manifest-attested only; no Lean compilation"}
    if path is None:
        return result
    packet = json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    if packet.get("schema") != "repo-dna-snapshots/v1" or packet.get("repository") != repository:
        raise ValueError("DNA schema or repository URL does not match")
    if not isinstance(packet.get("snapshots"), list):
        raise ValueError("DNA snapshots must be a list")
    generations, observed_commits = set(), set()
    for snapshot in packet["snapshots"]:
        commit, generation = snapshot.get("commit"), snapshot.get("generation")
        if not isinstance(commit, str) or not SHA.fullmatch(commit) or commit not in records:
            raise ValueError("DNA observation has missing or unknown full commit SHA")
        if commit in observed_commits:
            raise ValueError("only one DNA generation per commit is accepted in one packet")
        observed_commits.add(commit)
        if not isinstance(generation, str) or not generation.strip() or generation in generations:
            raise ValueError("DNA generation is empty, duplicated, or conflicting")
        generations.add(generation)
        provenance = snapshot.get("provenance", {})
        binding = provenance.get("binding")
        if binding not in {"source-verified", "unverified"}:
            raise ValueError("DNA binding must be source-verified or unverified")
        if binding == "source-verified" and (
            provenance.get("source_commit") != commit or provenance.get("working_tree_clean") is not True
            or any(not isinstance(provenance.get(k), str) or not provenance[k].strip()
                   for k in ("build_fingerprint", "toolchain"))
        ):
            raise ValueError("DNA source-verified manifest is incomplete or inconsistent")
        declarations = snapshot.get("declarations")
        if not isinstance(declarations, list):
            raise ValueError("DNA declarations must be a list")
        names = set()
        for row in declarations:
            name = row.get("name")
            if not isinstance(name, str) or not name.strip() or name in names:
                raise ValueError("DNA declaration name is missing or duplicated")
            names.add(name)
            if row.get("schema") == "hive.packet.expr_fingerprint.v1" or row.get("provenance", {}).get("method") == "metadata_proxy_v1":
                raise ValueError("metadata proxy rows are not compiled declaration DNA")
            if not any(row.get(field) for field in ("typeDigest", "valueDigest", "typeFingerprint", "valueFingerprint")):
                raise ValueError("declaration has no compiler fingerprint")
            for field in ("typeDigest", "valueDigest", "typeFingerprint", "valueFingerprint", "shapeHash"):
                item = row.get(field)
                if item is None:
                    continue
                if not isinstance(item, dict) or not isinstance(item.get("algorithmVersion"), str) or not item["algorithmVersion"].strip():
                    raise ValueError(f"{field} needs an explicit algorithmVersion")
                if field.endswith("Digest"):
                    if not isinstance(item.get("digest"), str) or not DIGEST.fullmatch(item["digest"]) or type(item.get("openTerm")) is not bool:
                        raise ValueError(f"invalid {field} SHA-256 digest or openTerm flag")
                else:
                    check_uint64(item.get("shapeHash"))
            for field in ("canonicalTypeHash", "canonicalValueHash", "dagShapeHash"):
                if row.get(field) is not None:
                    check_uint64(row[field])
        if binding == "unverified" or commit not in included:
            result["unattached"].append({"reason": "unverified provenance" if binding == "unverified" else "outside selected window", "snapshot": snapshot})
        else:
            result["snapshots"].append(snapshot)
    return result


def check_uint64(value):
    if not isinstance(value, str) or not value.isascii() or not value.isdecimal() or int(value) >= 2**64:
        raise ValueError("UInt64 fingerprints must remain decimal strings")


def expanded_edges(links):
    edges = Counter()
    for link in links:
        path = [link["source"], *link["chain"], link["target"]]
        for index, (parent, child) in enumerate(zip(path, path[1:])):
            parent_index = link["parent_index"] if index == len(path) - 2 else 0
            edges[parent, child, parent_index] += 1
    return edges


def export(repo, since, until, repository, dna_path=None):
    start, stop = utc(since), utc(until)
    if stop <= start:
        raise ValueError("until must follow since")
    records, order, refs, ignored, shallow = collect_history(repo)
    main = next((row["sha"] for row in refs if row["name"] == "origin/main"), None)
    main_chain = assign_lanes(records, order, main)
    commits = [records[sha] for sha in order if start.timestamp() <= records[sha]["time"] < stop.timestamp()]
    included = {row["sha"] for row in commits}
    if not included:
        raise ValueError("no reachable commits in selected UTC window")
    dna = load_dna(dna_path, repository, records, included)
    view = {row["sha"]: row for row in commits}
    children, original = defaultdict(list), Counter()
    for row in commits:
        for index, parent in enumerate(row["parents"]):
            children[parent].append(row["sha"])
            original[parent, row["sha"], index] += 1
            if parent not in view:
                previous = records.get(parent)
                view[parent] = dict(previous) if previous else {
                    "sha": parent, "parents": [], "time": None, "subject": "Unresolved parent at history boundary",
                    "refs": [], "index": row["index"] - 0.5, "lane": row["lane"],
                }
                view[parent].update(boundary=True, boundary_reason="outside-window" if previous else "unresolved-parent")
    keep = {sha for sha, row in view.items() if row["boundary"] or len(row["parents"]) != 1 or len(children[sha]) != 1 or row["refs"]}
    months = set()
    for row in commits:
        if row["sha"] in main_chain:
            month = datetime.fromtimestamp(row["time"], timezone.utc).strftime("%Y-%m")
            if month not in months:
                months.add(month)
                keep.add(row["sha"])
                row["checkpoint"] = month
    for snapshot in dna["snapshots"]:
        sha = snapshot["commit"]
        keep.add(sha)
        view[sha].setdefault("dna_generations", []).append(snapshot["generation"])
    links = []
    for row in commits:
        if row["sha"] not in keep:
            continue
        for index, parent in enumerate(row["parents"]):
            hidden = []
            while parent not in keep:
                hidden.append(parent)
                parent = view[parent]["parents"][0]
            links.append({"source": parent, "target": row["sha"], "kind": "first-parent" if index == 0 else "merge",
                          "parent_index": index, "hidden_count": len(hidden), "chain": list(reversed(hidden))})
    if expanded_edges(links) != original:
        raise ValueError("compression did not partition the original parent edges")
    nodes = sorted((view[sha] for sha in keep), key=lambda row: (row["index"], row["sha"]))
    stats = {
        "commit_count": len(commits), "parent_edges": sum(original.values()),
        "merge_commits": sum(len(row["parents"]) > 1 for row in commits),
        "forks": sum(len(children[row["sha"]]) > 1 for row in commits),
        "root_commits": sum(not row["parents"] for row in commits),
        "terminal_commits": sum(not children[row["sha"]] for row in commits),
        "branch_refs": sum(row["kind"] == "branch" for row in refs),
        "tag_refs": sum(row["kind"] == "tag" for row in refs),
        "clock_skew_edges": sum(records[parent]["time"] > records[child]["time"] for parent, child, _ in original if parent in records),
        "dna_snapshot_count": len(dna["snapshots"]),
        "visible_nodes": len(nodes), "boundary_nodes": sum(row["boundary"] for row in nodes),
    }
    return {"schema": "repo-phylogeny/v1", "repository": repository,
            "source": {"head": git(repo, "rev-parse", "HEAD").stdout.strip(), "generated_at": iso(datetime.now(timezone.utc)),
                       "refs": refs, "ignored_refs": ignored, "is_shallow": shallow,
                       "ref_scope": "current origin branches and tags (reachable history only)",
                       "reachable_commit_count": len(records),
                       "provenance_validation": "manifest contract only; no Lean compilation"},
            "window": {"since": iso(start), "until": iso(stop), "end_exclusive": True},
            "stats": stats, "commits": commits, "nodes": nodes, "links": links, "dna": dna}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ("repo", "since", "until", "repository-url", "out"):
        parser.add_argument("--" + flag, required=True)
    parser.add_argument("--dna")
    args = parser.parse_args()
    try:
        result = export(Path(args.repo), args.since, args.until, args.repository_url, args.dna)
        target = Path(args.out)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(result, ensure_ascii=False, separators=(",", ":")) + "\n", encoding="utf-8")
        print(json.dumps(result["stats"], sort_keys=True))
    except (ValueError, OSError, KeyError, TypeError, AttributeError, subprocess.CalledProcessError) as exc:
        print(f"export failed: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
