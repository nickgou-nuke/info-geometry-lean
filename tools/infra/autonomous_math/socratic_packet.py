#!/usr/bin/env python3
"""Packetize Socratic alchemy loop outputs into the autonomous_math evidence format."""

from __future__ import annotations

import re
from typing import Any

from .evidence_packet import EvidenceClaim, EvidencePacket, FormalizationTarget


_SECTION_RE = re.compile(r"^([A-Z_ ]+):\s*$", re.MULTILINE)
_THEOREM_RE = re.compile(r"\b(?:theorem|lemma|def|axiom|structure)\s+([A-Za-z0-9_'.]+)\b")


def _extract_tagged_block(text: str, tag: str) -> str:
    marker = f"{tag}:"
    idx = text.find(marker)
    if idx == -1:
        return ""
    rest = text[idx + len(marker) :]
    m = _SECTION_RE.search(rest)
    if m:
        return rest[: m.start()].strip()
    return rest.strip()


def _theorem_targets(lean_code: str) -> list[FormalizationTarget]:
    out: list[FormalizationTarget] = []
    for name in _THEOREM_RE.findall(lean_code or "")[:12]:
        kind = "theorem"
        if lean_code.find(f"def {name}") != -1:
            kind = "definition"
        elif lean_code.find(f"structure {name}") != -1:
            kind = "definition"
        out.append(FormalizationTarget(kind=kind, name=name))
    return out


def build_packet_from_loop(run_data: dict[str, Any]) -> EvidencePacket:
    original_prompt = str(run_data.get("original_prompt", "")).strip()
    gemini_rounds = run_data.get("gemini_rounds", [])
    codex_critiques = run_data.get("codex_critiques", [])
    lean_rounds = run_data.get("lean_rounds", [])
    compile_attempts = run_data.get("compile_attempts", [])
    compiled_decl_extractions = run_data.get("compiled_decl_extractions", [])
    fallback_info = run_data.get("fallback_info", {})

    evidence: list[EvidenceClaim] = []
    candidate_invariants: list[str] = []
    open_problems: list[str] = []
    formalization_targets: list[FormalizationTarget] = []

    if isinstance(gemini_rounds, list):
        for i, text in enumerate(gemini_rounds, start=1):
            body = str(text).strip()
            if not body:
                continue
            distilled = _extract_tagged_block(body, "DISTILLED CONCEPT") or body.splitlines()[0]
            evidence.append(
                EvidenceClaim(
                    claim=distilled,
                    sources=[f"gemini_round_{i}"],
                    confidence="medium",
                    evidence_summary=f"Gemini round {i} distilled concept or leading thesis.",
                )
            )
            if distilled and distilled not in candidate_invariants:
                candidate_invariants.append(distilled)

    if isinstance(codex_critiques, list):
        for i, text in enumerate(codex_critiques, start=1):
            body = str(text).strip()
            if not body:
                continue
            nucleus = _extract_tagged_block(body, "NUCLEUS")
            if nucleus:
                evidence.append(
                    EvidenceClaim(
                        claim=nucleus,
                        sources=[f"codex_critique_{i}"],
                        confidence="high",
                        evidence_summary=f"Codex critique round {i} nucleus extraction.",
                    )
                )
                if nucleus not in candidate_invariants:
                    candidate_invariants.append(nucleus)
            amp = _extract_tagged_block(body, "AMPLIFICATION_VECTOR")
            if amp and amp not in open_problems:
                open_problems.append(amp)

    if isinstance(fallback_info, dict) and fallback_info:
        recovered = str(fallback_info.get("concept", "")).strip()
        source_mode = str(fallback_info.get("mode", "fallback"))
        source_path = str(fallback_info.get("path", "")).strip()
        if recovered:
            evidence.append(
                EvidenceClaim(
                    claim=recovered,
                    sources=[f"gemini_limit_fallback:{source_mode}"],
                    confidence="medium",
                    evidence_summary=f"Recovered concept from {source_mode} fallback source {source_path or '[unknown path]'}.",
                )
            )
            if recovered not in candidate_invariants:
                candidate_invariants.append(recovered)
        target_names = fallback_info.get("target_names", [])
        if isinstance(target_names, list):
            for name in target_names[:12]:
                target = str(name).strip()
                if target:
                    formalization_targets.append(
                        FormalizationTarget(kind="theorem", name=target, note="Recovered from fallback packet while Gemini daily limit was active.")
                    )

    if isinstance(lean_rounds, list):
        for lean in lean_rounds:
            formalization_targets.extend(_theorem_targets(str(lean)))

    if isinstance(compiled_decl_extractions, list):
        for row in compiled_decl_extractions:
            if not isinstance(row, dict):
                continue
            round_no = int(row.get("round", 0) or 0)
            module_name = str(row.get("module_name", "")).strip()
            decl_names = row.get("decl_names", [])
            if not isinstance(decl_names, list):
                continue
            if decl_names:
                evidence.append(
                    EvidenceClaim(
                        claim=f"Accepted Lean environment exported {len(decl_names)} declaration(s) for round {round_no} in module {module_name or '[unknown module]'}.",
                        sources=[f"compiled_decl_extraction_{round_no}"],
                        confidence="high",
                        evidence_summary=", ".join(str(name).strip() for name in decl_names[:8] if str(name).strip()),
                    )
                )
            for name in decl_names[:24]:
                decl = str(name).strip()
                if not decl:
                    continue
                kind = "theorem"
                lowered = decl.lower()
                if ".inst" in lowered or lowered.startswith("inst"):
                    kind = "definition"
                formalization_targets.append(
                    FormalizationTarget(
                        kind=kind,
                        name=decl,
                        note=f"Accepted declaration name extracted from compiled Lean environment for round {round_no}.",
                    )
                )

    if isinstance(compile_attempts, list):
        for attempt in compile_attempts:
            if not isinstance(attempt, dict):
                continue
            returncode = attempt.get("returncode", 1)
            try:
                returncode_int = int(1 if returncode is None else returncode)
            except Exception:
                returncode_int = 1
            if returncode_int != 0:
                stderr = str(attempt.get("stderr", "")).strip()
                stdout = str(attempt.get("stdout", "")).strip()
                err = stderr or stdout or f"compile round {attempt.get('round', '?')} failed"
                if err not in open_problems:
                    open_problems.append(err)

    phase_log = [
        {"phase": "socratic_alchemy", "rounds": len(gemini_rounds) if isinstance(gemini_rounds, list) else 0},
        {"phase": "codex_critique", "rounds": len(codex_critiques) if isinstance(codex_critiques, list) else 0},
        {"phase": "lean_generation", "rounds": len(lean_rounds) if isinstance(lean_rounds, list) else 0},
        {"phase": "compile_attempts", "rounds": len(compile_attempts) if isinstance(compile_attempts, list) else 0},
        {"phase": "compiled_decl_extraction", "rounds": len(compiled_decl_extractions) if isinstance(compiled_decl_extractions, list) else 0},
    ]
    if isinstance(fallback_info, dict) and fallback_info:
        phase_log.append(
            {
                "phase": "gemini_limit_fallback",
                "source_mode": str(fallback_info.get("mode", "")),
                "source_path": str(fallback_info.get("path", "")),
                "trigger_round": int(fallback_info.get("trigger_round", 0) or 0),
            }
        )

    packet = EvidencePacket(
        research_goal=original_prompt or str(run_data.get("run_name", "socratic-alchemy-loop")),
        evidence=evidence,
        open_problems=open_problems[:24],
        candidate_invariants=candidate_invariants[:24],
        forbidden_moves=[
            "treat future-pass dialogue output as already theorem-backed",
            "promote symbolic amplification directly into canonical Lean without audit",
            "ignore compiler feedback when Codex-generated Lean fails",
        ],
        formalization_targets=formalization_targets[:24],
        phase_log=phase_log,
    )
    return packet
