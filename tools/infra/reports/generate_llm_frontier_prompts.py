#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.reports.common import read_text, repo_root, write_text
else:
    from tools.infra.reports.common import read_text, repo_root, write_text


DEFAULT_FRONTIER_CONTEXT = "skills/info-geometry-repo/references/frontier-prompt.md"
DEFAULT_CANDIDATE_PACKET = "skills/info-geometry-repo/references/bridge-candidates.md"
DEFAULT_THINNESS_INDEX = "BRIDGE_THINNESS_INDEX.md"
DEFAULT_CREATIVE_OUT = "skills/info-geometry-repo/references/frontier-prompt-creative.md"
DEFAULT_CRITICAL_OUT = "skills/info-geometry-repo/references/frontier-prompt-critical.md"


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        description=(
            "Generate a dual-lane LLM prompt pair from the current trusted frontier: "
            "a creative bridge-proposal prompt and a critical/formal-evaluation prompt."
        )
    )
    ap.add_argument("--frontier-context", default=DEFAULT_FRONTIER_CONTEXT)
    ap.add_argument("--candidate-packet", default=DEFAULT_CANDIDATE_PACKET)
    ap.add_argument("--thinness-index", default=DEFAULT_THINNESS_INDEX)
    ap.add_argument("--creative-out", default=DEFAULT_CREATIVE_OUT)
    ap.add_argument("--critical-out", default=DEFAULT_CRITICAL_OUT)
    return ap.parse_args()

def render_creative(frontier_context: str, candidate_packet: str) -> str:
    lines: list[str] = []
    lines.append("# Frontier Prompt: Creative Lane")
    lines.append("")
    lines.append("Use this prompt with a creative frontier-expansion model.")
    lines.append("Suggested role mapping: Gemini-style exploratory proposal lane.")
    lines.append("")
    lines.append("The model is allowed to extend the frontier imaginatively, but it is not")
    lines.append("allowed to claim proofs or authority beyond the trusted context below.")
    lines.append("")
    lines.append("## Hard Constraints")
    lines.append("")
    lines.append("- Do not claim any statement is proved.")
    lines.append("- Do not invent nonexistent imports, defs, theorems, or modules.")
    lines.append("- Stay inside the current repo vocabulary unless a tiny helper definition is unavoidable.")
    lines.append("- Prefer small bridge lemmas over giant new frameworks.")
    lines.append("- You may propose genuinely new morphisms or functional-program interfaces, but you must label them as proposals.")
    lines.append("- Treat frontier packets as proposal artifacts, not proof artifacts.")
    lines.append("")
    lines.append("## Task")
    lines.append("")
    lines.append("Propose 5 candidate bridge statements that could close real gaps in the current")
    lines.append("compiled theory graph.")
    lines.append("")
    lines.append("Bias toward:")
    lines.append("- missing quantum/transport bridges")
    lines.append("- operator / AQFT / Majorana / Bogoliubov seams if the packet suggests them")
    lines.append("- small morphisms that connect already existing nodes")
    lines.append("- statements that could later survive Lean hardening")
    lines.append("")
    lines.append("For each candidate provide exactly:")
    lines.append("1. `name`")
    lines.append("2. `Lean-style signature sketch`")
    lines.append("3. `which graph gap it closes`")
    lines.append("4. `why it might be genuinely new within this framework`")
    lines.append("5. `likely proof ingredients already present in repo`")
    lines.append("6. `risk level` (`low` / `medium` / `high`)")
    lines.append("")
    lines.append("Do not output proof scripts.")
    lines.append("Do not output more than 5 candidates.")
    lines.append("")
    lines.append("## Trusted Frontier Context")
    lines.append("")
    lines.append("```md")
    lines.append(frontier_context)
    lines.append("```")
    lines.append("")
    lines.append("## Current Candidate Packet")
    lines.append("")
    lines.append("```md")
    lines.append(candidate_packet)
    lines.append("```")
    lines.append("")
    lines.append("## Output Discipline")
    lines.append("")
    lines.append("- Novelty means new theorem content inside the current formal framework, not community validation.")
    lines.append("- If a candidate looks like a rename, re-export, or definitional equality, say so and discard it.")
    lines.append("- If a candidate needs a missing concept, mark that concept explicitly as a proposed helper.")
    return "\n".join(lines) + "\n"


def render_critical(frontier_context: str, candidate_packet: str, thinness_index: str) -> str:
    lines: list[str] = []
    lines.append("# Frontier Prompt: Critical Lane")
    lines.append("")
    lines.append("Use this prompt with a critical Lean-aware evaluation model.")
    lines.append("Suggested role mapping: ChatGPT/Codex-style formal critique lane.")
    lines.append("")
    lines.append("The model must aggressively reject fake closure, thin bridges, and unsupported")
    lines.append("speculation. It is not allowed to promote a candidate just because it sounds")
    lines.append("mathematically interesting.")
    lines.append("")
    lines.append("## Hard Constraints")
    lines.append("")
    lines.append("- Treat the creative lane output as untrusted proposal text.")
    lines.append("- Reject any candidate that invents unsupported repo vocabulary.")
    lines.append("- Reject any candidate whose likely proof is just `rfl`, direct forwarding, or tuple repackaging unless the name is explicitly downgraded.")
    lines.append("- Do not claim proof completion.")
    lines.append("- Convert only credible candidates into minimal Lean-facing theorem sketches, attack plans, and quarantine-ready concrete sketches when justified.")
    lines.append("")
    lines.append("## Task")
    lines.append("")
    lines.append("Evaluate the creative-lane candidate list against the current trusted frontier")
    lines.append("and the current thin-bridge audit.")
    lines.append("")
    lines.append("For each candidate provide exactly:")
    lines.append("1. `verdict` (`accept` / `revise` / `reject`)")
    lines.append("2. `reason`")
    lines.append("3. `minimal Lean-style signature sketch`")
    lines.append("4. `proof ingredients already present in repo`")
    lines.append("5. `thinness risk` (`definitional` / `forwarder` / `packaging` / `substantive`) ")
    lines.append("6. `quarantine recommendation` (`yes` / `no`) ")
    lines.append("7. `Lean-ready materialization sketch` (`none` unless the candidate is concrete and recommended for quarantine) ")
    lines.append("")
    lines.append("Then end with:")
    lines.append("- `Top 3 survivors`")
    lines.append("- `Top 3 rejection reasons`")
    lines.append("")
    lines.append("## Paste Creative Output Below")
    lines.append("")
    lines.append("```text")
    lines.append("[PASTE CREATIVE MODEL OUTPUT HERE]")
    lines.append("```")
    lines.append("")
    lines.append("## Trusted Frontier Context")
    lines.append("")
    lines.append("```md")
    lines.append(frontier_context)
    lines.append("```")
    lines.append("")
    lines.append("## Current Candidate Packet")
    lines.append("")
    lines.append("```md")
    lines.append(candidate_packet)
    lines.append("```")
    lines.append("")
    lines.append("## Current Thin-Bridge Audit")
    lines.append("")
    lines.append("```md")
    lines.append(thinness_index)
    lines.append("```")
    lines.append("")
    lines.append("## Review Discipline")
    lines.append("")
    lines.append("- Prefer candidates that can become small insertable lemmas.")
    lines.append("- Downgrade grand names if the likely proof is only structural packaging.")
    lines.append("- If a candidate survives, keep it small enough for quarantine first and canonical promotion later.")
    lines.append("- A materialization sketch must be compilable Lean syntax in the current repo vocabulary; it may be a small quarantine wrapper over already existing theorems.")
    return "\n".join(lines) + "\n"

def main() -> int:
    args = parse_args()
    root = repo_root()

    frontier_context = read_text(root / args.frontier_context)
    candidate_packet = read_text(root / args.candidate_packet)
    thinness_index = read_text(root / args.thinness_index)

    creative = render_creative(frontier_context, candidate_packet)
    critical = render_critical(frontier_context, candidate_packet, thinness_index)

    creative_path = root / args.creative_out
    critical_path = root / args.critical_out
    write_text(creative_path, creative)
    write_text(critical_path, critical)

    print(f"[generate-llm-frontier-prompts] wrote {creative_path}")
    print(f"[generate-llm-frontier-prompts] wrote {critical_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
