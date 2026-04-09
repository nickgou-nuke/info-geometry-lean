#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.reports.common import normalize_user_path, repo_root
else:
    from tools.infra.reports.common import normalize_user_path, repo_root


DEFAULT_SURROGATE_INDEX = "SURROGATE_INDEX.md"
DEFAULT_VACUITY_INDEX = "VACUITY_INDEX.md"
DEFAULT_THINNESS_INDEX = "BRIDGE_THINNESS_INDEX.md"
DEFAULT_OUT = "skills/info-geometry-repo/references/debt-candidates.md"

PRIORITY_ORDER = {"critical": 0, "high": 1, "medium": 2, "low": 3}
INDEX_ORDER = {"surrogate": 0, "vacuity": 1, "thinness": 2}
INDEX_LABELS = {
    "surrogate": "surrogate debt",
    "vacuity": "vacuity debt",
    "thinness": "thin-bridge debt",
}
DECL_START_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|axiom)\s+([A-Za-z0-9_'.]+)"
)
DECL_BOUNDARY_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|axiom)\s+[A-Za-z0-9_'.]+"
)
ATTRIBUTE_LINE_RE = re.compile(r"^\s*@\[[^\]]+\]\s*$")
QUEUE_RE = re.compile(
    r"^- `(?P<priority>[^`]+)` `(?P<category>[^`]+)` (?P<name>.+?) at `(?P<file>[^`:]+)(?::(?P<line>\d+))?`$"
)


@dataclass(frozen=True)
class DebtSignal:
    index_name: str
    priority: str
    category: str
    name: str
    file: str
    line: int | None


@dataclass
class DebtTarget:
    name: str
    file: str
    line: int | None
    signals: list[DebtSignal] = field(default_factory=list)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate a debt-targeted replacement packet from the tracked surrogate, "
            "vacuity, and thin-bridge audits."
        )
    )
    parser.add_argument("--surrogate-index", default=DEFAULT_SURROGATE_INDEX)
    parser.add_argument("--vacuity-index", default=DEFAULT_VACUITY_INDEX)
    parser.add_argument("--thinness-index", default=DEFAULT_THINNESS_INDEX)
    parser.add_argument("--out", default=DEFAULT_OUT)
    parser.add_argument("--top", type=int, default=12)
    return parser.parse_args()

def file_bucket(rel: str) -> str:
    if "/Unstable/" in rel or "/Archive/" in rel:
        return "unstable"
    if "/Canonical/" in rel:
        return "canonical"
    return "stable"


def normalize_name(raw: str) -> str:
    return raw.strip().strip("`")


def parse_queue(path: Path, index_name: str) -> list[DebtSignal]:
    if not path.exists():
        return []
    signals: list[DebtSignal] = []
    active_queue = False
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        stripped = raw_line.strip()
        if stripped.startswith("## "):
            active_queue = stripped in {"## Queue", "## Aggressive Replacement Queue"}
            continue
        if not active_queue:
            continue
        match = QUEUE_RE.match(stripped)
        if not match:
            continue
        signals.append(
            DebtSignal(
                index_name=index_name,
                priority=match.group("priority"),
                category=match.group("category"),
                name=normalize_name(match.group("name")),
                file=match.group("file"),
                line=int(match.group("line")) if match.group("line") else None,
            )
        )
    return signals


def aggregate_targets(signals: list[DebtSignal]) -> list[DebtTarget]:
    grouped: dict[tuple[str, str], DebtTarget] = {}
    for signal in signals:
        key = (signal.file, signal.name)
        target = grouped.get(key)
        if target is None:
            target = DebtTarget(name=signal.name, file=signal.file, line=signal.line)
            grouped[key] = target
        elif target.line is None or (
            signal.line is not None and signal.line < target.line
        ):
            target.line = signal.line
        target.signals.append(signal)
    return list(grouped.values())


def strongest_priority(target: DebtTarget) -> str:
    return min(target.signals, key=lambda signal: PRIORITY_ORDER.get(signal.priority, 9)).priority


def risk_for_target(target: DebtTarget) -> str:
    priority = strongest_priority(target)
    if priority in {"critical", "high"}:
        return "high"
    if priority == "medium":
        return "medium"
    return "low"


def sort_targets(targets: list[DebtTarget]) -> list[DebtTarget]:
    def key(target: DebtTarget) -> tuple[int, int, str, int, str]:
        priority = strongest_priority(target)
        bucket = file_bucket(target.file)
        bucket_order = 0 if bucket == "canonical" else 1 if bucket == "stable" else 2
        line = target.line if target.line is not None else 10**9
        return (
            PRIORITY_ORDER.get(priority, 9),
            bucket_order,
            target.file,
            line,
            target.name,
        )

    return sorted(targets, key=key)


def slugify(value: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9_]+", "_", value)
    slug = re.sub(r"_+", "_", slug).strip("_")
    return slug or "debt_target"


def locate_decl_start(lines: list[str], approx_line: int | None, name: str) -> int | None:
    pattern = re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?"
        rf"(?:theorem|lemma|def|abbrev|structure|class|instance|axiom)\s+{re.escape(name)}\b"
    )
    if approx_line is None:
        search_ranges = [(0, len(lines))]
    else:
        center = max(0, approx_line - 1)
        search_ranges = [
            (max(0, center - 12), min(len(lines), center + 40)),
            (0, len(lines)),
        ]
    for start, stop in search_ranges:
        for idx in range(start, stop):
            if pattern.match(lines[idx]):
                return idx
    return None


def extract_signature(root: Path, target: DebtTarget) -> str:
    path = root / target.file
    fallback = (
        f"theorem {target.name}\n"
        "    : Prop := by\n"
        "  -- constructive replacement target generated from the tracked debt packet"
    )
    if not path.exists():
        return fallback
    lines = path.read_text(encoding="utf-8").splitlines()
    start = locate_decl_start(lines, target.line, target.name)
    if start is None:
        return fallback
    while start > 0 and ATTRIBUTE_LINE_RE.match(lines[start - 1]):
        start -= 1
    collected: list[str] = []
    for idx in range(start, min(len(lines), start + 120)):
        line = lines[idx]
        if idx > start and DECL_BOUNDARY_RE.match(line):
            break
        collected.append(line)
        if ":=" in line:
            break
    head = "\n".join(collected).strip()
    if not head:
        return fallback
    if ":=" in head:
        head = head.split(":=", 1)[0].rstrip()
    return (
        f"{head} := by\n"
        "  -- constructive replacement target generated from the tracked debt packet"
    )


def nearby_declarations(root: Path, target: DebtTarget, limit: int = 6) -> list[str]:
    path = root / target.file
    if not path.exists():
        return []
    lines = path.read_text(encoding="utf-8").splitlines()
    center = max(0, (target.line or 1) - 1)
    start = max(0, center - 120)
    stop = min(len(lines), center + 120)
    found: list[str] = []
    for idx in range(start, stop):
        match = DECL_START_RE.match(lines[idx])
        if not match:
            continue
        name = match.group(1)
        if name == target.name or name in found:
            continue
        found.append(name)
        if len(found) >= limit:
            break
    return found


def category_hint(index_name: str, category: str) -> str:
    hints = {
        ("surrogate", "proof_hole"): "replace the explicit proof hole with a real Lean proof",
        ("surrogate", "axiom_decl"): "replace the explicit axiom with a proved theorem surface",
        ("surrogate", "quarantine_manifest"): "repair the quarantine bookkeeping so every unstable debt surface is tracked by a live module or removed",
        ("surrogate", "prop_constant"): "replace the constant Prop surface with a theorem that relates real existing structures",
        ("surrogate", "trivial_theorem"): "replace the trivial proof with a constructive derivation from load-bearing hypotheses",
        ("surrogate", "universal_true_field"): "replace the universal-True field with a real invariant or remove the empty interface",
        ("surrogate", "zero_quadratic_form"): "replace the zero quadratic-form surrogate with the intended constructed quadratic form",
        ("surrogate", "scaled_zero_quadratic_form"): "replace the scaled-zero quadratic-form surrogate with a genuine nonzero construction",
        ("surrogate", "conditional_theorem"): "eliminate the conditional wrapper by proving the missing obligation constructively",
        ("surrogate", "contract_decl"): "replace the open contract surface with a concrete proved interface or theorem",
        ("surrogate", "contract_constructor"): "reduce dependence on contract constructors by proving the target directly from concrete data",
        ("surrogate", "surrogate_marker"): "remove the placeholder-marked surface by replacing it with a proved construction",
        ("vacuity", "carrier_alias"): "replace the alias-driven bridge with a mathematically explicit transport layer",
        ("vacuity", "identity_transport"): "replace identity transport with a proved transport theorem",
        ("vacuity", "uninstantiated_bridge_assumption"): "replace the theorem-surface bridge witness with a constructed realization or prove the result from existing concrete data",
        ("vacuity", "explicit_vacuity_marker"): "remove the explicit alias-model compatibility layer from the active path",
        ("thinness", "definitional_identity"): "replace the definitional identity with a substantive proof",
        ("thinness", "direct_forwarder"): "replace the direct forwarder with a local constructive derivation",
        ("thinness", "underscore_hypothesis"): "replace hidden placeholder hypotheses with explicit constructive assumptions or proved facts",
        ("thinness", "package_orchestration"): "shrink the packaging theorem into direct theorem content or helper lemmas",
    }
    return hints.get((index_name, category), "replace the tracked debt surface with a constructive proof")


def render_packet(targets: list[DebtTarget], all_signals: list[DebtSignal], root: Path, top: int) -> str:
    chosen = sort_targets(targets)[:top]
    counts_by_index = {name: 0 for name in INDEX_LABELS}
    for signal in all_signals:
        counts_by_index[signal.index_name] = counts_by_index.get(signal.index_name, 0) + 1

    lines: list[str] = []
    lines.append("# Debt Candidates")
    lines.append("")
    lines.append("This note is a report-only constructive replacement queue derived from the tracked")
    lines.append("surrogate, vacuity, and thin-bridge audits.")
    lines.append("")
    lines.append("It is not a proof artifact.")
    lines.append("")
    lines.append("The purpose is to pin exact debt targets that can be attacked by a creative lane,")
    lines.append("shrunk by a critical lane, and then materialized into quarantine for Lean validation.")
    lines.append("")
    lines.append("## Audit Context")
    lines.append("")
    lines.append(f"- surrogate findings: `{counts_by_index.get('surrogate', 0)}`")
    lines.append(f"- vacuity findings: `{counts_by_index.get('vacuity', 0)}`")
    lines.append(f"- thin-bridge findings: `{counts_by_index.get('thinness', 0)}`")
    lines.append(f"- aggregated replacement targets: `{len(targets)}`")
    lines.append("")
    lines.append("## Selection Rule")
    lines.append("")
    lines.append("- Prefer canonical/stable declarations over unstable/archive surfaces.")
    lines.append("- Prefer critical/high findings over medium/low findings.")
    lines.append("- Aggregate duplicate targets when multiple audits point at the same declaration.")
    lines.append("- Keep every candidate tied to a real file:line surface already tracked by the audits.")

    if not chosen:
        lines.extend(
            [
                "",
                "## Current Replacement Queue",
                "",
                "- none",
                "",
                "The current tracked audits do not expose any replacement targets. Regenerate the packet after new debt findings appear.",
                "",
            ]
        )
        return "\n".join(lines)

    for ordinal, target in enumerate(chosen, start=1):
        sorted_signals = sorted(
            target.signals,
            key=lambda signal: (
                PRIORITY_ORDER.get(signal.priority, 9),
                INDEX_ORDER.get(signal.index_name, 9),
                signal.category,
            ),
        )
        signature = extract_signature(root, target)
        nearby = nearby_declarations(root, target)
        strongest = strongest_priority(target)
        signal_summary = ", ".join(
            f"{signal.index_name}:{signal.category} ({signal.priority})" for signal in sorted_signals
        )
        replacement_goals = "; ".join(
            category_hint(signal.index_name, signal.category) for signal in sorted_signals
        )
        lines.extend(
            [
                "",
                f"## Candidate {ordinal}",
                "",
                "`name`",
                "",
                f"`DebtCandidate.repair_{slugify(target.name)}_{ordinal}`",
                "",
                "`Lean-style signature sketch`",
                "",
                "```lean",
                signature,
                "```",
                "",
                "`why this closes a real frontier edge`",
                "",
                (
                    f"This candidate targets the tracked debt surface `{target.name}` at "
                    f"`{target.file}:{target.line or 0}`. It aggregates the audit signals "
                    f"`{signal_summary}`. A successful replacement would {replacement_goals}."
                ),
                "",
                "`likely proof ingredients already present in repo`",
                "",
                f"- `target file: {target.file}`",
                f"- `target line: {target.line or 0}`",
                f"- `strongest priority: {strongest}`",
                f"- `audit signals: {signal_summary}`",
            ]
        )
        if nearby:
            lines.append(f"- `nearby declarations: {', '.join(nearby)}`")
        for signal in sorted_signals[:3]:
            lines.append(
                f"- `{INDEX_LABELS.get(signal.index_name, signal.index_name)} goal: {category_hint(signal.index_name, signal.category)}`"
            )
        lines.extend(
            [
                "",
                "`risk level`",
                "",
                f"`{risk_for_target(target)}`",
            ]
        )

    lines.append("")
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    root = repo_root()
    surrogate_index = normalize_user_path(args.surrogate_index, root / args.surrogate_index)
    vacuity_index = normalize_user_path(args.vacuity_index, root / args.vacuity_index)
    thinness_index = normalize_user_path(args.thinness_index, root / args.thinness_index)
    out_path = normalize_user_path(args.out, root / args.out)

    signals = []
    signals.extend(parse_queue(surrogate_index, "surrogate"))
    signals.extend(parse_queue(vacuity_index, "vacuity"))
    signals.extend(parse_queue(thinness_index, "thinness"))
    targets = aggregate_targets(signals)

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(render_packet(targets, signals, root, top=args.top), encoding="utf-8")
    print(f"[generate-debt-candidates] wrote {out_path}")
    print(
        f"[generate-debt-candidates] signals={len(signals)} aggregated_targets={len(targets)} emitted={min(args.top, len(targets))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
