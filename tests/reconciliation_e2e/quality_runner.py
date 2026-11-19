"""Scoped quality, axiom, header, native_decide, and Prop-wrapper runners.

Follows e2e_explorer_quality/handoff.md §4 strictly:
- Always passes explicit target paths or dotted module names (never unscoped).
- Redirects semantic_content_audit outputs strictly to scratch/e2e_reconciliation/reports/.
- Never passes --quarantine to opengauss_screener.py.
- Parses axiom_index.py --json axiom_usage keys against ALLOWED_AXIOMS rather than
  trusting axiom_index.py exit code alone.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

from tests.reconciliation_e2e import ALLOWED_AXIOMS, REPO_ROOT, REPORTS_DIR
from tools.quality.audit_constructivity import strip_comments
from tools.quality.proof_proxy_staged_gate import (
    REQUIRED_LEAN_COPYRIGHT_HEADER,
    aggregate_prop_constructors,
)

PYTHON_EXE: str = sys.executable

# Baseline untouched historical files lacking byte-0 Apache 2.0 2026 header at Phase 0.
# Per e2e_spec_miner_rubric §1.1 item 5, these are informational warnings when untouched
# in baseline mode and hard failures if modified by M1/M2/M3 or audited in strict M4 mode.
BASELINE_HEADER_EXEMPT: frozenset[str] = frozenset(
    {
        "lean/InfoGeometry/Canonical/OperatorFrechetForms.lean",
        "lean/InfoGeometry/Thermo/OnsagerDifferentialFormsBridge.lean",
        "lean/InfoGeometry/Canonical/Erlangen20OperatorGeometryDatum.lean",
        "lean/InfoGeometry/Canonical/ErlangenOperator2.lean",
        "lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean",
        "lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean",
        "lean/InfoGeometry/KK/ClNNFredholmBridge.lean",
        "lean/InfoGeometry/KK/RealSplitKreinEquivarianceBridge.lean",
        "lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean",
        "lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean",
        "lean/InfoGeometry/Geometry/PhaseErlanger.lean",
        "lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean",
        "lean/InfoGeometry/Krein/DoubleRealKreinShearDefect.lean",
        "lean/InfoGeometry/Topology/CliffordMobiusDeRhamMonodromy.lean",
        "lean/InfoGeometry/Krein/DoubledMatrixSymplectic.lean",
        "lean/InfoGeometry/Krein/KreinSpace.lean",
        "lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean",
        "lean/InfoGeometry/KK/RealCl55KasparovCycleBridge.lean",
        "lean/InfoGeometry/Canonical/ErlangenOperator2Bridge.lean",
        "lean/InfoGeometry/Canonical/ConnesNCGFormAlgebra.lean",
        "lean/InfoGeometry/OperatorAlgebra/KreinFrechetRiesz.lean",
        "lean/InfoGeometry/Canonical/FelixKleinGeometryUnification.lean",
        "lean/InfoGeometry/Canonical/OperatorErlangenGaloisConnection.lean",
        "lean/InfoGeometry/Erlangen/SmoothCartanGeometry.lean",
        "lean/InfoGeometry/Lie/KreinCl44SplitG2DerivationPosetSynthesis.lean",
        "lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean",
        "lean/InfoGeometry/Clifford/Cl11SupergradedTensorBridge.lean",
        "lean/InfoGeometry/Clifford/Cl11CliffordMapIsometryBridge.lean",
        "lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean",
        "lean/InfoGeometry/Canonical/FrechetCECovariantConnection.lean",
        "lean/InfoGeometry/Algebra/NonAssocDerivation.lean",
        "lean/InfoGeometry/Geometry/AssociativeGaugeConnection.lean",
        "lean/InfoGeometry/Thermo/OnsagerOperatorClosure.lean",
        "lean/InfoGeometry/NCG/NoncommutativeCyclicCocycle.lean",
        "lean/InfoGeometry/OperatorAlgebra/DerivationGaugeTransport.lean",
        "lean/InfoGeometry/Canonical/SplitCliffordMatrixLimitSoldering.lean",
        "lean/InfoGeometry/Projective/KleinQuadric.lean",
        "lean/InfoGeometry/Projective/KleinQuadricPlucker.lean",
        "lean/InfoGeometry/Projective/ExteriorPluckerTower.lean",
        "lean/InfoGeometry/Projective/MobiusPluckerKleinCompatibility.lean",
    }
)


_TOOL_CACHE: dict[tuple[str, tuple[str, ...]], ToolResult] = {}


@dataclass
class ToolResult:
    name: str
    passed: bool
    returncode: int
    summary: str
    details: dict[str, Any] = field(default_factory=dict)


def _norm_paths(paths: Iterable[str | Path]) -> list[str]:
    result: list[str] = []
    for p in paths:
        path = Path(p)
        if path.is_absolute():
            path = path.relative_to(REPO_ROOT)
        result.append(path.as_posix())
    if not result:
        raise ValueError("Scoped quality checks require at least one explicit target path")
    return result


def lean_path_to_module(rel_path: str) -> str:
    p = Path(rel_path)
    if p.is_absolute():
        p = p.relative_to(REPO_ROOT)
    parts = p.with_suffix("").parts
    if parts[0] in ("lean", "src"):
        parts = parts[1:]
    return ".".join(parts)


def _run_cmd(cmd: list[str], timeout: int = 180) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def _extract_leading_json_list(stdout: str) -> list[dict[str, Any]]:
    decoder = json.JSONDecoder()
    pos = 0
    while True:
        idx = stdout.find("[", pos)
        if idx == -1:
            break
        try:
            data, _ = decoder.raw_decode(stdout, idx)
        except json.JSONDecodeError:
            pos = idx + 1
            continue
        if isinstance(data, list) and all(isinstance(item, dict) for item in data):
            return data
        pos = idx + 1
    raise ValueError(f"Could not locate JSON list in stdout: {stdout[:300]!r}")


def _extract_trailing_json(stdout: str) -> dict[str, Any]:
    idx = stdout.rfind("\n{")
    start = idx + 1 if idx != -1 else stdout.find("{")
    if start == -1:
        raise ValueError(f"Could not locate JSON payload in stdout: {stdout[:300]!r}")
    decoder = json.JSONDecoder()
    data, _ = decoder.raw_decode(stdout[start:])
    if not isinstance(data, dict):
        raise ValueError(f"Expected JSON dict, got {type(data).__name__}")
    return data


def _git_modified_or_untracked() -> set[str]:
    proc = _run_cmd(["git", "status", "--porcelain"], timeout=30)
    if proc.returncode != 0:
        return set()
    changed: set[str] = set()
    for line in proc.stdout.splitlines():
        if len(line) < 4:
            continue
        path_part = line[3:].strip()
        if " -> " in path_part:
            path_part = path_part.split(" -> ", 1)[1].strip()
        changed.add(path_part)
    return changed


def run_placeholder_audit(paths: Iterable[str | Path]) -> ToolResult:
    targets = tuple(_norm_paths(paths))
    key = ("placeholder_audit", targets)
    if key in _TOOL_CACHE:
        return _TOOL_CACHE[key]
    proc = _run_cmd(
        [PYTHON_EXE, "tools/quality/placeholder_audit.py", "--strict", "--format", "json", *targets]
    )
    data = json.loads(proc.stdout) if proc.stdout.strip() else {}
    summary = data.get("summary", {})
    hard = int(
        summary.get(
            "hard_count",
            summary.get("provenance", {}).get("hard_failures", -1),
        )
    )
    passed = proc.returncode == 0 and hard == 0
    res = ToolResult(
        name="placeholder_audit",
        passed=passed,
        returncode=proc.returncode,
        summary=f"hard_count={hard}, findings={summary.get('finding_count', '?')}",
        details=data,
    )
    _TOOL_CACHE[key] = res
    return res


def run_axiom_audit(paths: Iterable[str | Path]) -> ToolResult:
    targets = tuple(_norm_paths(paths))
    key = ("axiom_audit", targets)
    if key in _TOOL_CACHE:
        return _TOOL_CACHE[key]
    proc = _run_cmd(
        [PYTHON_EXE, "tools/infra/axiom_audit.py", "--fail-on-gaps", "--format", "json", *targets]
    )
    data = json.loads(proc.stdout) if proc.stdout.strip() else {}
    gaps = int(data.get("total_open_gaps", -1))
    passed = proc.returncode == 0 and gaps == 0
    res = ToolResult(
        name="axiom_audit",
        passed=passed,
        returncode=proc.returncode,
        summary=f"clean_files={data.get('clean_files', '?')}, total_open_gaps={gaps}",
        details=data,
    )
    _TOOL_CACHE[key] = res
    return res


def run_detect_hollow_theorems(paths: Iterable[str | Path]) -> ToolResult:
    targets = tuple(_norm_paths(paths))
    key = ("detect_hollow_theorems", targets)
    if key in _TOOL_CACHE:
        return _TOOL_CACHE[key]
    proc = _run_cmd([PYTHON_EXE, "tools/quality/detect_hollow_theorems.py", "--strict", *targets])
    passed = proc.returncode == 0
    res = ToolResult(
        name="detect_hollow_theorems",
        passed=passed,
        returncode=proc.returncode,
        summary=(proc.stdout.strip() or proc.stderr.strip() or "ok")[:240],
        details={"stdout": proc.stdout, "stderr": proc.stderr},
    )
    _TOOL_CACHE[key] = res
    return res


def run_semantic_vacuity_gate(paths: Iterable[str | Path]) -> ToolResult:
    targets = tuple(_norm_paths(paths))
    key = ("semantic_vacuity_gate", targets)
    if key in _TOOL_CACHE:
        return _TOOL_CACHE[key]
    proc = _run_cmd(
        [PYTHON_EXE, "tools/quality/semantic_vacuity_gate.py", "--fail-on", "error", *targets]
    )
    passed = proc.returncode == 0
    res = ToolResult(
        name="semantic_vacuity_gate",
        passed=passed,
        returncode=proc.returncode,
        summary=(proc.stdout.strip() or proc.stderr.strip() or "ok")[:240],
        details={"stdout": proc.stdout, "stderr": proc.stderr},
    )
    _TOOL_CACHE[key] = res
    return res


def run_repo_lean_scope_audit(paths: Iterable[str | Path]) -> ToolResult:
    targets = tuple(_norm_paths(paths))
    key = ("repo_lean_scope_audit", targets)
    if key in _TOOL_CACHE:
        return _TOOL_CACHE[key]
    proc = _run_cmd(
        [
            PYTHON_EXE,
            "tools/quality/repo_lean_scope_audit.py",
            "--fail-on",
            "authoritative",
            "--format",
            "json",
            *targets,
        ]
    )
    data = json.loads(proc.stdout) if proc.stdout.strip() else {}
    debt = int(data.get("debt_findings", -1))
    passed = proc.returncode == 0 and debt == 0
    res = ToolResult(
        name="repo_lean_scope_audit",
        passed=passed,
        returncode=proc.returncode,
        summary=f"debt_files={data.get('debt_files', '?')}, debt_findings={debt}",
        details=data,
    )
    _TOOL_CACHE[key] = res
    return res


def run_opengauss_screener(paths: Iterable[str | Path]) -> ToolResult:
    targets = tuple(_norm_paths(paths))
    key = ("opengauss_screener", targets)
    if key in _TOOL_CACHE:
        return _TOOL_CACHE[key]
    proc = _run_cmd([PYTHON_EXE, "tools/infra/opengauss_screener.py", "--json", *targets])
    data = json.loads(proc.stdout) if proc.stdout.strip() else {}
    violations = data.get("violations", {})
    error_count = 0
    warning_count = 0
    for items in violations.values():
        for item in items:
            sev = str(item.get("severity", "")).upper()
            if sev == "ERROR":
                error_count += 1
            elif sev == "WARNING":
                warning_count += 1
    passed = proc.returncode == 0 and error_count == 0
    res = ToolResult(
        name="opengauss_screener",
        passed=passed,
        returncode=proc.returncode,
        summary=f"errors={error_count}, warnings={warning_count}",
        details=data,
    )
    _TOOL_CACHE[key] = res
    return res


def run_unified_gate(paths: Iterable[str | Path]) -> ToolResult:
    targets = tuple(_norm_paths(paths))
    key = ("unified_gate", targets)
    if key in _TOOL_CACHE:
        return _TOOL_CACHE[key]
    proc = _run_cmd([PYTHON_EXE, "tools/quality/unified_gate.py", *targets], timeout=240)
    passed = proc.returncode == 0
    res = ToolResult(
        name="unified_gate",
        passed=passed,
        returncode=proc.returncode,
        summary=(proc.stdout.strip() or proc.stderr.strip() or "ok")[:240],
        details={"stdout": proc.stdout, "stderr": proc.stderr},
    )
    _TOOL_CACHE[key] = res
    return res


def run_semantic_content_audit(paths: Iterable[str | Path], tag: str) -> ToolResult:
    targets = _norm_paths(paths)
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    safe_tag = re.sub(r"[^A-Za-z0-9_.-]+", "_", tag)
    json_out = REPORTS_DIR / f"sca_{safe_tag}.json"
    md_out = REPORTS_DIR / f"sca_{safe_tag}.md"
    cmd = [PYTHON_EXE, "tools/quality/semantic_content_audit.py"]
    for t in targets:
        cmd.extend(["--file-prefix", t])
    cmd.extend(
        [
            "--gate",
            "--no-manifest-consistency",
            "--json-out",
            str(json_out),
            "--md-out",
            str(md_out),
        ]
    )
    proc = _run_cmd(cmd, timeout=240)
    data = json.loads(json_out.read_text(encoding="utf-8")) if json_out.is_file() else {}
    blocking = int(data.get("summary", {}).get("blocking_finding_count", -1))
    passed = proc.returncode == 0 and blocking == 0
    return ToolResult(
        name="semantic_content_audit",
        passed=passed,
        returncode=proc.returncode,
        summary=f"blocking={blocking}, json_out={json_out.relative_to(REPO_ROOT)}",
        details=data,
    )


_AXIOM_CHECK_CACHE: dict[str, dict[str, Any]] = {}
_AXIOM_INDEX_CACHE: dict[tuple[str, ...], ToolResult] = {}
_AXIOM_INDEX_MOD_CACHE: dict[str, dict[str, Any]] = {}


def prewarm_axiom_index(modules: Iterable[str]) -> None:
    mods = [m for m in dict.fromkeys(modules) if m not in _AXIOM_INDEX_MOD_CACHE]
    if not mods:
        return
    try:
        proc = _run_cmd(
            [PYTHON_EXE, "tools/infra/axiom_index.py", "--batch", "0", "--timeout", "600", "--json", *mods],
            timeout=2400,
        )
    except subprocess.TimeoutExpired:
        return
    if not proc.stdout.strip():
        return
    try:
        data = _extract_trailing_json(proc.stdout)
    except Exception:
        data = {}
    suspicious = data.get("suspicious", {}) if isinstance(data, dict) else {}
    suspicious_mods = {
        occ[0]
        for occs in suspicious.values()
        for occ in occs
        if isinstance(occ, (list, tuple)) and occ
    }
    line_rx = re.compile(
        r"^\s*\[\d+/\d+\]\s+(\S+):\s+([✓!])\s+(\d+)\s+decls,\s+(\d+)✗\s+(\d+)p\s+(\d+)u\s*$"
    )
    for line in proc.stdout.splitlines():
        m = line_rx.match(line)
        if m:
            mod, sym, decls, nstd, npart, nunsafe = m.groups()
            _AXIOM_INDEX_MOD_CACHE[mod] = {
                "module": mod,
                "decls": int(decls),
                "nonstandard": int(nstd),
                "partial": int(npart),
                "unsafe": int(nunsafe),
                "suspicious_mod": mod in suspicious_mods,
                "passed": (
                    sym == "✓"
                    and int(nstd) == 0
                    and int(npart) == 0
                    and int(nunsafe) == 0
                    and mod not in suspicious_mods
                ),
            }


def prewarm_axiom_check(modules: Iterable[str]) -> None:
    mods = [m for m in dict.fromkeys(modules) if m not in _AXIOM_CHECK_CACHE]
    if not mods:
        return
    try:
        proc = _run_cmd([PYTHON_EXE, "tools/infra/axiom_check.py", "--quiet", "--json", *mods], timeout=2400)
    except subprocess.TimeoutExpired:
        return
    if proc.stdout.strip():
        entries = _extract_leading_json_list(proc.stdout)
        for entry in entries:
            if "module" in entry:
                _AXIOM_CHECK_CACHE[entry["module"]] = entry


def run_axiom_check(modules: Iterable[str]) -> ToolResult:
    mods = list(dict.fromkeys(modules))
    if not mods:
        raise ValueError("Scoped axiom_check requires at least one explicit module")
    missing = [m for m in mods if m not in _AXIOM_CHECK_CACHE]
    if missing:
        proc = _run_cmd([PYTHON_EXE, "tools/infra/axiom_check.py", "--quiet", "--json", *missing], timeout=2400)
        entries = _extract_leading_json_list(proc.stdout) if proc.stdout.strip() else []
        for entry in entries:
            if "module" in entry:
                _AXIOM_CHECK_CACHE[entry["module"]] = entry
        rc = proc.returncode
    else:
        rc = 0
    selected = [_AXIOM_CHECK_CACHE[m] for m in mods if m in _AXIOM_CHECK_CACHE]
    failed = [e for e in selected if not bool(e.get("passed"))]
    passed = len(selected) == len(mods) and not failed
    return ToolResult(
        name="axiom_check",
        passed=passed,
        returncode=0 if passed else (rc or 1),
        summary=f"checked={len(selected)}, failed={len(failed)}",
        details={"entries": selected, "failed": failed},
    )


def run_axiom_index(modules: Iterable[str]) -> ToolResult:
    mods = tuple(dict.fromkeys(modules))
    if not mods:
        raise ValueError("Scoped axiom_index requires at least one explicit module")
    if all(m in _AXIOM_INDEX_MOD_CACHE for m in mods):
        entries = [_AXIOM_INDEX_MOD_CACHE[m] for m in mods]
        failed = [e for e in entries if not e["passed"]]
        return ToolResult(
            name="axiom_index",
            passed=not failed,
            returncode=0 if not failed else 1,
            summary=f"modules={len(mods)}, failed={len(failed)} (prewarmed LOCK_SH)",
            details={"entries": entries, "failed": failed},
        )
    if mods in _AXIOM_INDEX_CACHE:
        return _AXIOM_INDEX_CACHE[mods]
    proc = _run_cmd([PYTHON_EXE, "tools/infra/axiom_index.py", "--timeout", "600", "--json", *mods], timeout=2400)
    if proc.returncode != 0:
        return ToolResult(
            name="axiom_index",
            passed=False,
            returncode=proc.returncode,
            summary=f"axiom_index error: {proc.stderr.strip()[:200]}",
            details={"stdout": proc.stdout, "stderr": proc.stderr},
        )
    data = _extract_trailing_json(proc.stdout)
    axiom_usage = data.get("axiom_usage", {})
    disallowed = sorted(set(axiom_usage.keys()) - set(ALLOWED_AXIOMS))
    suspicious = data.get("suspicious", {})
    passed = not disallowed and not suspicious
    res = ToolResult(
        name="axiom_index",
        passed=passed,
        returncode=proc.returncode,
        summary=f"axioms={sorted(axiom_usage.keys())}, disallowed={disallowed}, suspicious={list(suspicious.keys())}",
        details=data,
    )
    _AXIOM_INDEX_CACHE[mods] = res
    return res


def check_apache_headers(
    paths: Iterable[str | Path],
    strict_all: bool = False,
    exempt_untouched: frozenset[str] = BASELINE_HEADER_EXEMPT,
) -> ToolResult:
    targets = _norm_paths(paths)
    dirty_paths = _git_modified_or_untracked() if not strict_all else set()
    hard_failures: list[str] = []
    warnings: list[str] = []
    for rel in targets:
        full = REPO_ROOT / rel
        if not full.is_file():
            hard_failures.append(f"{rel}: missing file")
            continue
        source = full.read_text(encoding="utf-8")
        if not source.startswith(REQUIRED_LEAN_COPYRIGHT_HEADER):
            if not strict_all and rel in exempt_untouched and rel not in dirty_paths:
                warnings.append(f"{rel}: untouched baseline lacks byte-0 Apache 2.0 header")
            else:
                hard_failures.append(f"{rel}: missing byte-0 Apache 2.0 2026 header")
    passed = not hard_failures
    return ToolResult(
        name="apache_header_byte0",
        passed=passed,
        returncode=0 if passed else 1,
        summary=f"hard_failures={len(hard_failures)}, warnings={len(warnings)}",
        details={"hard_failures": hard_failures, "warnings": warnings},
    )


def check_native_decide(paths: Iterable[str | Path]) -> ToolResult:
    targets = _norm_paths(paths)
    hits: list[str] = []
    pattern = re.compile(r"\bnative_decide\b")
    for rel in targets:
        full = REPO_ROOT / rel
        if not full.is_file():
            hits.append(f"{rel}: missing file")
            continue
        source = full.read_text(encoding="utf-8")
        cleaned = strip_comments(
            source, strip_strings=True, strip_quoted_identifiers=True
        )
        for lineno, line in enumerate(cleaned.splitlines(), start=1):
            if pattern.search(line):
                hits.append(f"{rel}:{lineno}: native_decide forbidden")
    passed = not hits
    return ToolResult(
        name="native_decide_scan",
        passed=passed,
        returncode=0 if passed else 1,
        summary=f"hits={len(hits)}",
        details={"hits": hits},
    )


def check_prop_wrappers(paths: Iterable[str | Path]) -> ToolResult:
    targets = _norm_paths(paths)
    findings: list[dict[str, str]] = []
    for rel in targets:
        full = REPO_ROOT / rel
        if not full.is_file():
            findings.append({"file": rel, "type": "missing", "decl": "file not found"})
            continue
        source = full.read_text(encoding="utf-8")
        for type_name, decl_header in aggregate_prop_constructors(source):
            findings.append({"file": rel, "type": type_name, "decl": decl_header})
    passed = not findings
    return ToolResult(
        name="aggregate_prop_constructors",
        passed=passed,
        returncode=0 if passed else 1,
        summary=f"findings={len(findings)}",
        details={"findings": findings},
    )


_BUNDLE_CACHE: dict[tuple[tuple[str, ...], bool, bool, bool], dict[str, ToolResult]] = {}


def run_quality_bundle(
    paths: Iterable[str | Path],
    tag: str,
    *,
    strict_headers: bool = False,
    include_unified_gate: bool = True,
    include_sca: bool = False,
    use_cache: bool = True,
) -> dict[str, ToolResult]:
    targets = tuple(_norm_paths(paths))
    cache_key = (targets, strict_headers, include_unified_gate, include_sca)
    if use_cache and cache_key in _BUNDLE_CACHE:
        return _BUNDLE_CACHE[cache_key]

    results: dict[str, ToolResult] = {
        "placeholder_audit": run_placeholder_audit(targets),
        "axiom_audit": run_axiom_audit(targets),
        "detect_hollow_theorems": run_detect_hollow_theorems(targets),
        "semantic_vacuity_gate": run_semantic_vacuity_gate(targets),
        "repo_lean_scope_audit": run_repo_lean_scope_audit(targets),
        "opengauss_screener": run_opengauss_screener(targets),
        "apache_header_byte0": check_apache_headers(targets, strict_all=strict_headers),
        "native_decide_scan": check_native_decide(targets),
        "aggregate_prop_constructors": check_prop_wrappers(targets),
    }
    if include_unified_gate:
        results["unified_gate"] = run_unified_gate(targets)
    if include_sca:
        results["semantic_content_audit"] = run_semantic_content_audit(targets, tag)

    if use_cache:
        _BUNDLE_CACHE[cache_key] = results
    return results


def assert_quality_bundle_passed(results: dict[str, ToolResult], context: str) -> None:
    failures = [
        f"{name}: {res.summary}"
        for name, res in results.items()
        if not res.passed
    ]
    if failures:
        raise AssertionError(
            f"Quality bundle failed for {context}:\n  - " + "\n  - ".join(failures)
        )
