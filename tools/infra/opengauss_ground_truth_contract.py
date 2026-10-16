#!/usr/bin/env python3
"""Validate source-bound OpenGauss theorem contracts.

The contract records a human-authored mathematical interpretation. Validation
recomputes file and receipt fingerprints and checks quoted source excerpts; it
does not certify the interpretation, Lean typing, or proof status.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator


SCHEMA = "info_geometry.opengauss.ground_truth_theorem_contract.v1"
DISCOVERY_SCHEMA = "info_geometry.opengauss.discovery_report.v1"
DRAFT_RECEIPT_SCHEMA = "info_geometry.opengauss.contract_bound_draft.v1"


def _qualified_declarations(source: str) -> set[str]:
    """Extract declaration names while tracking namespace and section scopes."""
    return set(_qualified_declaration_heads(source))


def _qualified_declaration_heads(source: str) -> dict[str, list[dict[str, Any]]]:
    """Return source-located declaration headers, excluding comments and local `where` declarations.

    This is a source locator, not a Lean parser or elaborator. Consumers still
    need kernel checking for the declaration's actual type and proof status.
    """
    from tools.infra.opengauss_screener import (
        _strip_lean_comments_and_strings,
        _top_level_assignment_index,
    )

    clean_lines = _strip_lean_comments_and_strings(source).splitlines()
    raw_lines = source.splitlines()
    scopes: list[tuple[str, str]] = []
    found: dict[str, list[dict[str, Any]]] = {}
    namespace_pattern = re.compile(r"^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$")
    section_pattern = re.compile(r"^\s*section(?:\s+([A-Za-z0-9_'.]+))?\s*$")
    end_pattern = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_'.]+))?\s*$")
    declaration_pattern = re.compile(
        r"^\s*(?:(?:@\[[^\]]*\]\s*)*)"
        # `private` names are compiler-mangled and cannot truthfully be
        # represented by the ordinary namespace-qualified spelling here.
        r"(?:(?:protected|noncomputable|unsafe)\s+)*"
        r"(?P<kind>theorem|lemma|def|abbrev|opaque|structure|class|inductive)\s+"
        r"(?P<name>«[^»]+»|[A-Za-z_][A-Za-z0-9_']*)(?:\b|\s|$)"
    )
    command_boundary = re.compile(
        r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
        r"(?:theorem|lemma|def|abbrev|opaque|structure|class|inductive|namespace|section|end)\b"
    )
    last_top_level_indent: int | None = None

    for index, line in enumerate(clean_lines):
        namespace_match = namespace_pattern.match(line)
        if namespace_match:
            scopes.append(("namespace", namespace_match.group(1)))
            last_top_level_indent = None
            continue
        section_match = section_pattern.match(line)
        if section_match:
            scopes.append(("section", section_match.group(1) or ""))
            last_top_level_indent = None
            continue
        end_match = end_pattern.match(line)
        if end_match:
            closing = end_match.group(1)
            if closing is None:
                if scopes:
                    scopes.pop()
            else:
                match_index = next(
                    (
                        i for i in range(len(scopes) - 1, -1, -1)
                        if scopes[i][1] == closing
                        or (scopes[i][0] == "namespace" and scopes[i][1].split(".")[-1] == closing)
                    ),
                    None,
                )
                if match_index is not None:
                    del scopes[match_index:]
            last_top_level_indent = None
            continue
        declaration_match = declaration_pattern.match(line)
        if declaration_match is None:
            continue

        indent = len(line) - len(line.lstrip())
        if last_top_level_indent is not None and indent > last_top_level_indent:
            continue
        last_top_level_indent = indent
        namespaces = [
            component
            for kind, name in scopes if kind == "namespace"
            for component in name.split(".")
        ]
        qualified_name = ".".join([*namespaces, declaration_match.group("name")])

        header_lines: list[str] = []
        end_index = index
        for next_index in range(index, len(clean_lines)):
            candidate = clean_lines[next_index]
            candidate_indent = len(candidate) - len(candidate.lstrip())
            if next_index > index and command_boundary.match(candidate) and candidate_indent <= indent:
                break
            header_lines.append(candidate)
            end_index = next_index
            joined = " ".join(part.strip() for part in header_lines)
            assignment = _top_level_assignment_index(joined)
            if assignment is not None:
                header_lines = [joined[:assignment]]
                break
            if re.match(r"^\s*where\b", candidate):
                break

        joined_header = " ".join(part.strip() for part in header_lines).strip()
        # If the assignment was found, the statement is already cut before it.
        # A declaration without a value (for example an opaque declaration) is
        # retained through its source command boundary.
        hit = {
            "kind": declaration_match.group("kind"),
            "source_line": index + 1,
            "source_end_line": end_index + 1,
            "lean_statement": joined_header,
            "source_excerpt": "\n".join(raw_lines[index:end_index + 1]).strip(),
        }
        found.setdefault(qualified_name, []).append(hit)
    return found


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def _fail(message: str) -> None:
    raise ValueError(message)


def _nonempty(value: Any, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        _fail(f"{field} must be a non-empty string")
    return value.strip()


def _repo_file(root: Path, rel: Any, field: str) -> tuple[Path, str]:
    rel_text = _nonempty(rel, field)
    rel_path = Path(rel_text)
    if rel_path.is_absolute() or ".." in rel_path.parts:
        _fail(f"{field} must be a repository-relative path without traversal")
    resolved_root = root.resolve()
    resolved = (resolved_root / rel_path).resolve()
    if rel_path.as_posix() != rel_text:
        _fail(f"{field} must use its canonical repository-relative spelling")
    if resolved_root not in resolved.parents:
        _fail(f"{field} resolves outside the repository")
    if not resolved.is_file():
        _fail(f"{field} does not name an existing file: {rel_text}")
    return resolved, rel_path.as_posix()


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_contract_payload(contract: Any, *, repo_root: Path) -> dict[str, Any]:
    """Validate source and receipt bindings and return normalized digest data.

    Human-authored semantic fields are checked for presence only. In
    particular, ``status_assertion`` is recorded but never independently
    promoted to a Lean proof fact by this validator.
    """
    if not isinstance(contract, dict):
        _fail("ground-truth contract must be a JSON object")
    if contract.get("schema") != SCHEMA:
        _fail(f"unexpected ground-truth contract schema: {contract.get('schema')!r}")
    schema_path = Path(__file__).resolve().parents[2] / "tools" / "schema" / "ground_truth_theorem_contract.schema.json"
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    schema_errors = sorted(
        Draft202012Validator(schema).iter_errors(contract),
        key=lambda error: tuple(str(part) for part in error.absolute_path),
    )
    if schema_errors:
        first = schema_errors[0]
        location = "/".join(str(part) for part in first.absolute_path)
        _fail(f"contract schema violation at {location or '<root>'}: {first.message}")
    contract_id = _nonempty(contract.get("contract_id"), "contract_id")
    if contract.get("semantic_status") != "human_asserted_not_kernel_verified":
        _fail("semantic_status must be human_asserted_not_kernel_verified")
    _nonempty(contract.get("claim"), "claim")

    carrier = contract.get("carrier")
    if not isinstance(carrier, dict):
        _fail("carrier must be an object")
    _nonempty(carrier.get("type"), "carrier.type")
    for key in ("operations", "conventions"):
        values = carrier.get(key)
        if not isinstance(values, list) or any(not isinstance(item, str) or not item.strip() for item in values):
            _fail(f"carrier.{key} must be an array of non-empty strings")

    declarations = contract.get("owner_declarations")
    if not isinstance(declarations, list) or not declarations:
        _fail("owner_declarations must contain at least one source-grounded declaration")
    seen_names: set[str] = set()
    for index, declaration in enumerate(declarations):
        prefix = f"owner_declarations[{index}]"
        if not isinstance(declaration, dict):
            _fail(f"{prefix} must be an object")
        name = _nonempty(declaration.get("qualified_name"), f"{prefix}.qualified_name")
        if name in seen_names:
            _fail(f"duplicate owner declaration: {name}")
        seen_names.add(name)
        source, _ = _repo_file(repo_root, declaration.get("source_path"), f"{prefix}.source_path")
        expected_hash = declaration.get("source_sha256")
        if not isinstance(expected_hash, str) or not re.fullmatch(r"[0-9a-f]{64}", expected_hash):
            _fail(f"{prefix}.source_sha256 must be a lowercase SHA-256 digest")
        actual_hash = _sha256(source)
        if expected_hash != actual_hash:
            _fail(f"stale source hash for {name}: expected {expected_hash}, current {actual_hash}")
        excerpt = _nonempty(declaration.get("source_excerpt"), f"{prefix}.source_excerpt")
        normalize = lambda text: " ".join(text.split())
        source_text = source.read_text(encoding="utf-8")
        heads = _qualified_declaration_heads(source_text).get(name, [])
        source_line = declaration.get("source_line")
        source_end_line = declaration.get("source_end_line")
        expected_kind = declaration.get("kind")
        if type(source_line) is not int or type(source_end_line) is not int or source_line < 1 or source_end_line < source_line:
            _fail(f"{prefix} must identify a valid source_line/source_end_line range")
        matching_head = next(
            (
                head for head in heads
                if head["source_line"] == source_line
                and head["source_end_line"] == source_end_line
            ),
            None,
        )
        if matching_head is None:
            _fail(f"{name} has no declaration head at the cited source range")
        if expected_kind != matching_head["kind"]:
            _fail(f"kind for {name} differs from the parsed declaration head")
        actual_excerpt = "\n".join(source_text.splitlines()[source_line - 1:source_end_line]).strip()
        if normalize(excerpt) != normalize(actual_excerpt):
            _fail(f"source excerpt for {name} does not equal the cited declaration source range")
        statement = _nonempty(declaration.get("lean_statement"), f"{prefix}.lean_statement")
        if normalize(statement) != normalize(matching_head["lean_statement"]):
            _fail(f"lean_statement for {name} differs from the parsed declaration header")
        if declaration.get("status_assertion") not in {
            "asserted_proved", "assumption", "definition", "unverified"
        }:
            _fail(f"{prefix}.status_assertion must explicitly distinguish proof/assumption status")
        _nonempty(declaration.get("lean_statement"), f"{prefix}.lean_statement")

    for key in ("imports", "consumers", "out_of_scope"):
        values = contract.get(key)
        if not isinstance(values, list) or any(not isinstance(item, str) or not item.strip() for item in values):
            _fail(f"{key} must be an array of non-empty strings")
    if not contract["out_of_scope"]:
        _fail("out_of_scope must record at least one adjacent claim not established")

    gap = contract.get("smallest_gap")
    if not isinstance(gap, dict):
        _fail("smallest_gap must be an object")
    gap_name = _nonempty(gap.get("declaration_name"), "smallest_gap.declaration_name")
    gap_type = _nonempty(gap.get("lean_signature"), "smallest_gap.lean_signature")
    gap_expression = _nonempty(gap.get("pantograph_expression"), "smallest_gap.pantograph_expression")
    _nonempty(gap.get("description"), "smallest_gap.description")

    receipt = contract.get("discovery_receipt")
    if not isinstance(receipt, dict):
        _fail("discovery_receipt must bind the /discover JSON receipt")
    receipt_path, _ = _repo_file(repo_root, receipt.get("path"), "discovery_receipt.path")
    receipt_hash = receipt.get("sha256")
    if not isinstance(receipt_hash, str) or not re.fullmatch(r"[0-9a-f]{64}", receipt_hash):
        _fail("discovery_receipt.sha256 must be a lowercase SHA-256 digest")
    if _sha256(receipt_path) != receipt_hash:
        _fail("discovery receipt hash does not match its current bytes")
    try:
        report = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        _fail(f"discovery receipt is not readable JSON: {type(exc).__name__}")
    if not isinstance(report, dict) or report.get("schema") != DISCOVERY_SCHEMA:
        _fail("discovery receipt has an unexpected schema")
    if report.get("authority") != "navigation_only" or report.get("graph_is_proof_authority") is not False:
        _fail("discovery receipt must explicitly remain navigation-only")
    receipt_query = _nonempty(receipt.get("query"), "discovery_receipt.query")
    if report.get("query") != receipt_query:
        _fail("discovery receipt query differs from the contract binding")
    dag_context = report.get("dag_context")
    for context_name in ("dag_context", "local_dag_context"):
        context = report.get(context_name)
        if context is None:
            continue
        if not isinstance(context, dict):
            _fail(f"discovery receipt {context_name} must be an object or null")
        if context.get("validation_error") or context.get("status") == "invalid_packet":
            _fail(f"discovery receipt contains an invalid {context_name} packet")
        if context.get("authority") != "navigation_only" or context.get("graph_is_proof_authority") is not False:
            _fail(f"discovery receipt {context_name} must explicitly remain navigation-only")
        allowed_statuses = (
            {"ok", "unavailable", "unindexed", "not_found"}
            if context_name == "dag_context"
            else {"ok", "unavailable"}
        )
        if context.get("status") not in allowed_statuses:
            _fail(f"discovery receipt {context_name} has an unrecognized status")
        freshness = context.get("freshness")
        if freshness is None and context_name == "dag_context":
            provenance = context.get("graph_provenance")
            freshness = provenance.get("freshness") if isinstance(provenance, dict) else None
        if not isinstance(freshness, str) or not freshness:
            _fail(f"discovery receipt {context_name} must record graph freshness")
    carriers = report.get("carriers_found", [])
    lemmas = report.get("lemmas_found", [])
    if not isinstance(carriers, list) or not isinstance(lemmas, list):
        _fail("discovery receipt declaration results are malformed")
    reported_hits = carriers + lemmas
    for declaration in declarations:
        short_name = declaration["qualified_name"].split(".")[-1]
        matching_hit = any(
            isinstance(hit, dict)
            and hit.get("name") == short_name
            and hit.get("qualified_name") == declaration["qualified_name"]
            and hit.get("kind") == expected_kind
            and Path(str(hit.get("file", ""))).as_posix() == declaration["source_path"]
            and hit.get("source_sha256") == declaration["source_sha256"]
            and hit.get("line") == source_line
            and hit.get("source_end_line") == source_end_line
            and normalize(str(hit.get("lean_statement", ""))) == normalize(matching_head["lean_statement"])
            for hit in reported_hits
        )
        if not matching_hit:
            _fail(f"discovery receipt does not contain the cited current owner declaration {declaration['qualified_name']}")

    return {
        "contract": contract,
        "contract_id": contract_id,
        "contract_sha256": canonical_digest(contract),
        "missing_declaration_name": gap_name,
        "missing_lean_signature": gap_type,
        "pantograph_expression": gap_expression,
        "discovery_receipt_sha256": receipt_hash,
    }


def validate_draft_receipt_payload(receipt: Any, *, repo_root: Path) -> dict[str, Any]:
    """Validate the draft source snapshot and its separate Pantograph goal."""
    if not isinstance(receipt, dict) or receipt.get("schema") != DRAFT_RECEIPT_SCHEMA:
        _fail("draft receipt has an unexpected schema")
    contract = receipt.get("contract")
    checked = validate_contract_payload(contract, repo_root=repo_root)
    if receipt.get("contract_sha256") != checked["contract_sha256"]:
        _fail("draft receipt contract digest does not match its embedded contract")
    source, source_path = _repo_file(repo_root, receipt.get("source_path"), "draft_receipt.source_path")
    source_hash = _nonempty(receipt.get("source_sha256"), "draft_receipt.source_sha256")
    if not re.fullmatch(r"[0-9a-f]{64}", source_hash) or _sha256(source) != source_hash:
        _fail("draft receipt source hash does not match the current source snapshot")
    target_name = _nonempty(receipt.get("target_name"), "draft_receipt.target_name")
    if target_name != checked["missing_declaration_name"]:
        _fail("draft receipt target name differs from the contract gap")
    target_expression = _nonempty(receipt.get("target_expression"), "draft_receipt.target_expression")
    if target_expression != checked["pantograph_expression"]:
        _fail("draft receipt proposition differs from the contract Pantograph expression")
    signature = _nonempty(receipt.get("declaration_signature"), "draft_receipt.declaration_signature")
    declarations = _qualified_declaration_heads(source.read_text(encoding="utf-8")).get(target_name, [])
    normalize = lambda text: " ".join(text.split())
    if not any(normalize(item["lean_statement"]) == normalize(signature) for item in declarations):
        _fail("draft receipt declaration signature does not match its source snapshot")
    return {
        "contract": contract,
        "contract_sha256": checked["contract_sha256"],
        "target_name": target_name,
        "declaration_signature": signature,
        "target_expression": target_expression,
        "source_path": source_path,
        "source_sha256": source_hash,
    }


def load_and_validate_contract(path: Path, *, repo_root: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read ground-truth contract: {type(exc).__name__}") from exc
    result = validate_contract_payload(payload, repo_root=repo_root)
    result["contract_path"] = str(path.resolve())
    return result
