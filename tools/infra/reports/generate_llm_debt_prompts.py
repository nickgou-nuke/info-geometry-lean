#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.reports.common import read_text, write_text
else:
    from tools.infra.reports.common import read_text, write_text


DEFAULT_DEBT_PACKET = "skills/info-geometry-repo/references/debt-candidates.md"
DEFAULT_SURROGATE_INDEX = "SURROGATE_INDEX.md"
DEFAULT_VACUITY_INDEX = "VACUITY_INDEX.md"
DEFAULT_THINNESS_INDEX = "BRIDGE_THINNESS_INDEX.md"
DEFAULT_CREATIVE_OUT = "skills/info-geometry-repo/references/debt-prompt-creative.md"
DEFAULT_CRITICAL_OUT = "skills/info-geometry-repo/references/debt-prompt-critical.md"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate a dual-lane LLM prompt pair for constructive debt replacement: "
            "a creative attack-plan prompt and a critical minimization prompt."
        )
    )
    parser.add_argument("--debt-packet", default=DEFAULT_DEBT_PACKET)
    parser.add_argument("--surrogate-index", default=DEFAULT_SURROGATE_INDEX)
    parser.add_argument("--vacuity-index", default=DEFAULT_VACUITY_INDEX)
    parser.add_argument("--thinness-index", default=DEFAULT_THINNESS_INDEX)
    parser.add_argument("--creative-out", default=DEFAULT_CREATIVE_OUT)
    parser.add_argument("--critical-out", default=DEFAULT_CRITICAL_OUT)
    return parser.parse_args()

def render_creative(debt_packet: str, surrogate_index: str, vacuity_index: str, thinness_index: str) -> str:
    lines: list[str] = []
    lines.append("# Debt Prompt: Creative Lane")
    lines.append("")
    lines.append("Use this prompt with a proposal-oriented model that is trying to replace real")
    lines.append("tracked debt items, not invent new frontier prose.")
    lines.append("")
    lines.append("The model is allowed to suggest helper lemmas, proof decompositions, and local")
    lines.append("refactors, but it is not allowed to claim proof completion.")
    lines.append("")
    lines.append("## Hard Constraints")
    lines.append("")
    lines.append("- Do not claim that a theorem is proved.")
    lines.append("- Do not invent nonexistent repo vocabulary, imports, or helper lemmas.")
    lines.append("- Stay anchored to the exact debt targets in the packet below.")
    lines.append("- Prefer small helper lemmas and proof decomposition over giant rewrites.")
    lines.append("- If a target should be rejected as not worth automating, say so explicitly.")
    lines.append("- Treat the packet as a replacement queue, not a proof artifact.")
    lines.append("")
    lines.append("## Task")
    lines.append("")
    lines.append("For each candidate in the debt packet, propose the smallest constructive")
    lines.append("replacement path that could plausibly survive Lean validation.")
    lines.append("")
    lines.append("For each candidate provide exactly:")
    lines.append("1. `candidate name`")
    lines.append("2. `target theorem to repair`")
    lines.append("3. `proposed helper lemmas`")
    lines.append("4. `constructive attack plan`")
    lines.append("5. `likely existing repo ingredients`")
    lines.append("6. `risk level` (`low` / `medium` / `high`)")
    lines.append("")
    lines.append("Do not output full Lean proofs.")
    lines.append("Do not propose more than 3 helper lemmas per candidate.")
    lines.append("")
    lines.append("## Debt Packet")
    lines.append("")
    lines.append("```md")
    lines.append(debt_packet)
    lines.append("```")
    lines.append("")
    lines.append("## Surrogate Index")
    lines.append("")
    lines.append("```md")
    lines.append(surrogate_index)
    lines.append("```")
    lines.append("")
    lines.append("## Vacuity Index")
    lines.append("")
    lines.append("```md")
    lines.append(vacuity_index)
    lines.append("```")
    lines.append("")
    lines.append("## Thin-Bridge Index")
    lines.append("")
    lines.append("```md")
    lines.append(thinness_index)
    lines.append("```")
    lines.append("")
    lines.append("## Output Discipline")
    lines.append("")
    lines.append("- If the packet is empty, say there is currently no tracked debt target to repair.")
    lines.append("- If a candidate only needs renaming or deletion, say so instead of inventing proof work.")
    lines.append("- If a helper lemma would create a larger abstraction leak, reject it.")
    return "\n".join(lines) + "\n"


def render_critical(debt_packet: str, surrogate_index: str, vacuity_index: str, thinness_index: str) -> str:
    lines: list[str] = []
    lines.append("# Debt Prompt: Critical Lane")
    lines.append("")
    lines.append("Use this prompt with a Lean-aware review model that aggressively minimizes")
    lines.append("replacement plans before anything is materialized in quarantine.")
    lines.append("")
    lines.append("## Hard Constraints")
    lines.append("")
    lines.append("- Treat the creative-lane output as untrusted proposal text.")
    lines.append("- Reject invented helper lemmas or unsupported imports.")
    lines.append("- Reject plans that only restate the existing debt surface.")
    lines.append("- Reject plans that still reduce to `rfl`, direct forwarding, alias transport, or packaging assembly.")
    lines.append("- Keep only candidates small enough to materialize in quarantine first.")
    lines.append("")
    lines.append("## Task")
    lines.append("")
    lines.append("Evaluate the creative-lane replacement proposals against the tracked debt packet")
    lines.append("and the current debt audits.")
    lines.append("")
    lines.append("For each candidate provide exactly:")
    lines.append("1. `name`")
    lines.append("2. `review verdict` (`accept` / `revise` / `reject`)")
    lines.append("3. `review reason`")
    lines.append("4. `quarantine recommendation` (`yes` / `no`)")
    lines.append("5. `Lean-ready materialization sketch` (a fenced `lean` code block)")
    lines.append("6. `allowed helper lemmas`")
    lines.append("7. `blocked moves`")
    lines.append("")
    lines.append("Use the exact field labels above so downstream automation can parse reviewed")
    lines.append("materialization packets without manual normalization.")
    lines.append("")
    lines.append("Then end with:")
    lines.append("- `Top 3 materialization order`")
    lines.append("- `Top 3 rejection reasons`")
    lines.append("")
    lines.append("## Paste Creative Output Below")
    lines.append("")
    lines.append("```text")
    lines.append("[PASTE CREATIVE MODEL OUTPUT HERE]")
    lines.append("```")
    lines.append("")
    lines.append("## Debt Packet")
    lines.append("")
    lines.append("```md")
    lines.append(debt_packet)
    lines.append("```")
    lines.append("")
    lines.append("## Surrogate Index")
    lines.append("")
    lines.append("```md")
    lines.append(surrogate_index)
    lines.append("```")
    lines.append("")
    lines.append("## Vacuity Index")
    lines.append("")
    lines.append("```md")
    lines.append(vacuity_index)
    lines.append("```")
    lines.append("")
    lines.append("## Thin-Bridge Index")
    lines.append("")
    lines.append("```md")
    lines.append(thinness_index)
    lines.append("```")
    lines.append("")
    lines.append("## Review Discipline")
    lines.append("")
    lines.append("- Prefer direct repair of the tracked theorem over new wrapper layers.")
    lines.append("- If the best action is deletion, renaming, or theorem splitting, say so explicitly.")
    lines.append("- A surviving candidate should have a theorem header that the coding agent can materialize verbatim in quarantine.")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    root = repo_root()

    debt_packet = read_text(root / args.debt_packet)
    surrogate_index = read_text(root / args.surrogate_index)
    vacuity_index = read_text(root / args.vacuity_index)
    thinness_index = read_text(root / args.thinness_index)

    creative = render_creative(debt_packet, surrogate_index, vacuity_index, thinness_index)
    critical = render_critical(debt_packet, surrogate_index, vacuity_index, thinness_index)

    creative_path = root / args.creative_out
    critical_path = root / args.critical_out
    write_text(creative_path, creative)
    write_text(critical_path, critical)

    print(f"[generate-llm-debt-prompts] wrote {creative_path}")
    print(f"[generate-llm-debt-prompts] wrote {critical_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
