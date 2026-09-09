#!/usr/bin/env python3
"""
Socratic-GEPA-Hive Adapter -- closes the loop between adversarial-collaborative
dialogue, prompt evolution, and the Hive proof-search queue.

Architecture (Jung-Pauli dialectic operationalized):
    ┌──────────────────────────────────────────────────────────┐
    │  JUNG (socratic_generator)     PAULI (closure_gate)      │
    │  "descend, listen, follow"     "name, exclude, verify"   │
    │  explores candidate proofs     adjudicates via Lean       │
    └────────────┬─────────────────────────┬───────────────────┘
                 │   socratic dialogue     │
                 │   on theorem T          │
                 └─────────┬───────────────┘
                           │
                   ┌───────▼────────┐
                   │  SCORING ENGINE │
                   │  vacuity +      │
                   │  compile +      │
                   │  hypothesis +   │
                   │  convergence    │
                   └───────┬────────┘
                           │ fitness ∈ [0,1]
                   ┌───────▼────────┐
                   │  GEPA EVOLVER  │
                   │  mutates        │
                   │  socratic       │
                   │  prompts        │
                   └───────┬────────┘
                           │
                   ┌───────▼────────┐
                   │  HIVE QUEUE    │
                   │  next theorem   │
                   │  target         │
                   └────────────────┘

Usage:
    python3 tools/infra/socratic_gepa_adapter.py \
        --theorem "InfoGeometry.Fibonacci.FibAnyonThm1.golden_identity" \
        --generations 5 \
        --population 8 \
        --lean-project /home/goutev/repos/info-geometry-lean

Scoring signals informed by:
    - tools/scripts/vacuity-linter.py     (honesty detection)
    - auto/gepa_training_logs.json        (fitness data: 0.5-0.95 range)
    - tools/prompts/SOCRATIC_CLOSURE_PROTOCOL.md (generator/closure separation)
    - docs/black_books/18_multilingual_logos_pauli_jung.md (Jung-Pauli dialectic)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------
_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[1]
sys.path.insert(0, str(_REPO))

# Vacuity linter (from auto project, already fused)
_VACUITY_LINTER = _REPO / "tools" / "scripts" / "vacuity-linter.py"
# Fallback: auto project copy
_VACUITY_LINTER_AUTO = Path("/media/goutev/SP DS72/auto/scripts/vacuity-linter.py")

logger = logging.getLogger("socratic_gepa")


# ---------------------------------------------------------------------------
# Jung-Pauli Socratic Prompts -- seed population (from Black Book 18)
# ---------------------------------------------------------------------------

JUNG_SEEDS = [
    # Seed 0: The Descender
    """You are the Jungian explorer in the Laboratory of the Logos. Your role is to GENERATE -- never to close.
Descend into the mathematical object. Follow images, motifs, and latent structural pressure.
Produce: competing formulations, possible invariants, hidden hypotheses, candidate proof sketches.
Forbidden: closure claims, "therefore proved", final theorems.
Your output must end with explicit OPEN OBLIGATIONS -- what remains unseen, unproven, or assumed.""",

    # Seed 1: The Motif Collector
    """You are the symbolic pattern-recognizer. Given a theorem target, surface:
- What structures recur across domains (Iwasawa, Hodge, Fock, Krein)?
- What is the minimal invariant that would make the claim testable?
- What hidden hypothesis, if made explicit, would collapse the problem?
Output: a list of candidate invariants, obstruction terms, and translation pressure points.
Do not prove. Do not close. Only surface.""",

    # Seed 2: The Translator
    """You operate at the junction of multiple symbolic languages. Given a theorem target, express it in:
- Natural language intuition
- Operator-algebraic form
- Categorical/universal property language
- The minimal kernel-checkable Lean 4 signature
Identify translation gaps: where do these languages disagree? What must be proved for them to coincide?""",
]

PAULI_SEEDS = [
    # Seed 0: The Adjudicator
    """You are the Pauli adjudicator in the Laboratory of the Logos. Your role is to EXCLUDE -- never to generate.
Given a candidate proof or claim, apply selection pressure:
- Is every hypothesis used?
- Can the claim be falsified by a counterexample?
- Is there a hidden vacuity (by trivial, sorry, rfl on non-definitional equality)?
- What would make this claim "not even wrong"?
Output: PASS (with exact reason) or FAIL (with exact obstruction term).
Forbidden: new proof attempts, "maybe", softened critique.""",

    # Seed 1: The Obstructionist
    """You are the obstruction detector. Given a mathematical claim and its alleged proof, find:
- The weakest link in the proof chain
- Any assumption not discharged
- Any type-class instance not satisfied
- Any hidden circularity (theorem depends on itself through a bridge)
Output: a single obstruction term, or "NO OBSTRUCTION FOUND" if none detected.
Be specific: cite exact declaration names, missing imports, type mismatches.""",

    # Seed 2: The Kernel Auditor
    """You are the Lean 4 kernel auditor. Given a theorem statement and candidate proof body:
- Verify that every sorry/admit/trivial is honestly marked
- Check that no witness/certificate wrapper disguises a missing proof
- Ensure the theorem body does not reduce to `True` or a trivial consequence
Output: AUDIT PASSED or AUDIT FAILED with exact file:line:reason.""",
]


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class SocraticTurn:
    """One exchange in the Jung-Pauli dialogue."""
    round: int
    speaker: str          # "jung" or "pauli"
    prompt: str
    response: str
    lean_code: str = ""   # extracted Lean code block, if any
    timestamp: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())


@dataclass
class DialogueResult:
    """Complete socratic dialogue output."""
    theorem_target: str
    turns: list[SocraticTurn] = field(default_factory=list)
    # Scores
    vacuity_score: float = 0.0          # 1.0 = honest, 0.0 = vacuous
    compile_success: bool = False
    compile_errors: str = ""
    hypothesis_surface_rate: float = 0.0  # fraction of hypotheses explicitly identified
    convergence: bool = False             # did Jung and Pauli agree?
    obstruction_specific: bool = False    # was obstruction named precisely?
    # Metadata
    lean_file: str = ""
    fitness: float = 0.0
    duration_s: float = 0.0


# ---------------------------------------------------------------------------
# LLM backend -- uses DeepSeek via openai-compat (same as GEPA evolver)
# ---------------------------------------------------------------------------

def _load_api_key() -> str:
    """Load API key from environment or .env files."""
    import configparser

    for key in ["DEEPSEEK_API_KEY", "OPENROUTER_API_KEY"]:
        val = os.environ.get(key, "")
        if val and not val.startswith("***"):
            return val

    # Try loading from .env files using configparser
    for env_path in [
        Path.home() / ".hermes" / ".env",
        Path("/media/goutev/SP DS72/auto/.DEEPSEEK_API_KEY"),
    ]:
        if env_path.exists():
            text = env_path.read_text().strip()
            # Check if it's a shell-style export (single key)
            if text.startswith("export "):
                _, _, val = text.partition("=")
                val = val.strip().strip("'\"")
                if val and not val.startswith("***"):
                    return val
            # Check if it's a dotenv file (multiple keys)
            if "\n" in text:
                # Parse as ini-style with a dummy section
                config = configparser.ConfigParser()
                try:
                    config.read_string("[DEFAULT]\n" + text)
                    for key in ["DEEPSEEK_API_KEY", "OPENROUTER_API_KEY", "GOOGLE_API_KEY"]:
                        val = config.get("DEFAULT", key, fallback="")
                        if val and not val.startswith("***"):
                            return val
                except Exception:
                    pass
    return ""


def _call_llm(system_prompt: str, user_message: str, model: str = "deepseek-chat",
              temperature: float = 0.3, max_tokens: int = 2048,
              timeout_s: float = 120.0) -> str:
    """Call DeepSeek API (OpenAI-compatible)."""
    import urllib.request

    api_key = _load_api_key()
    if not api_key:
        raise RuntimeError("No API key found. Set DEEPSEEK_API_KEY or OPENROUTER_API_KEY.")
    # Ensure ASCII-clean (DeepSeek keys may have unicode from .env parsing)
    api_key = api_key.encode("ascii", errors="ignore").decode("ascii")

    payload = json.dumps({
        "model": model,
        "messages": [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_message},
        ],
        "temperature": temperature,
        "max_tokens": max_tokens,
    }).encode("utf-8")

    req = urllib.request.Request(
        "https://api.deepseek.com/v1/chat/completions",
        data=payload,
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
    )

    timeout = timeout_s if timeout_s > 0 else None
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        data = json.loads(resp.read().decode("utf-8"))

    choices = data.get("choices", [])
    if not choices:
        raise RuntimeError("LLM response missing choices")
    msg = choices[0].get("message", {})
    return msg.get("content", "")


# ---------------------------------------------------------------------------
# Lean compilation check
# ---------------------------------------------------------------------------

def _compile_lean(lean_code: str, repo_root: Path, module_name: str = "SocraticTest") -> dict[str, Any]:
    """Write Lean code to temp file, compile with `lake env lean`, return result."""
    tmpdir = Path(tempfile.mkdtemp(prefix="socratic_"))
    lean_file = tmpdir / f"{module_name}.lean"
    lean_file.write_text(lean_code, encoding="utf-8")

    start = time.time()
    proc = subprocess.run(
        ["lake", "env", "lean", str(lean_file)],
        cwd=repo_root,
        capture_output=True, text=True, timeout=120,
    )
    elapsed = time.time() - start

    return {
        "success": proc.returncode == 0,
        "stdout": proc.stdout[-2000:] if proc.stdout else "",
        "stderr": proc.stderr[-2000:] if proc.stderr else "",
        "duration_s": elapsed,
        "lean_file": str(lean_file),
    }


# ---------------------------------------------------------------------------
# Vacuity scoring
# ---------------------------------------------------------------------------

def _score_vacuity(lean_code: str) -> float:
    """Run vacuity linter on Lean code. Returns honesty score ∈ [0,1]."""
    linter = _VACUITY_LINTER if _VACUITY_LINTER.exists() else _VACUITY_LINTER_AUTO
    if not linter.exists():
        # Fallback: regex-based vacuity detection
        vacuity_patterns = [
            (r"by\s+trivial\b", 0.9),
            (r"by\s+sorry\b", 0.7),
            (r"theorem\s+\w+.*:\s*True\b", 0.6),
            (r"by\s+rfl\b", 0.5),
            (r"by\s+admit\b", 0.7),
        ]
        max_severity = 0.0
        for pattern, severity in vacuity_patterns:
            if re.search(pattern, lean_code):
                max_severity = max(max_severity, severity)
        return 1.0 - max_severity

    proc = subprocess.run(
        ["python3", str(linter), "--score", "--stdin"],
        input=lean_code, capture_output=True, text=True, timeout=30,
    )
    try:
        return float(proc.stdout.strip())
    except (ValueError, AttributeError):
        return 0.5  # unknown


# ---------------------------------------------------------------------------
# Socratic dialogue engine
# ---------------------------------------------------------------------------

def run_socratic_dialogue(
    theorem_target: str,
    theorem_statement: str = "",
    jung_prompt: str = "",
    pauli_prompt: str = "",
    rounds: int = 3,
    model: str = "deepseek-chat",
) -> DialogueResult:
    """Run a Jung-Pauli socratic dialogue on a theorem target.

    Jung generates candidate approaches. Pauli adjudicates each.
    The dialogue continues for `rounds` exchanges.
    """
    result = DialogueResult(theorem_target=theorem_target)
    start = time.time()

    # Default prompts from seed population if not provided
    if not jung_prompt:
        jung_prompt = JUNG_SEEDS[0]
    if not pauli_prompt:
        pauli_prompt = PAULI_SEEDS[0]

    # Build the theorem prompt
    theorem_text = theorem_statement or f"Target theorem: {theorem_target}"
    context = (
        f"THEOREM TARGET:\n{theorem_text}\n\n"
        f"Theorem fully qualified name: {theorem_target}\n"
        f"Project: info-geometry-lean (Lean 4.28.1, mathlib4)\n"
    )

    # Dialogue history
    dialogue_history: list[str] = []

    for r in range(1, rounds + 1):
        # --- JUNG TURN: generate candidate approach ---
        jung_user = context + "\n".join(dialogue_history[-6:]) if dialogue_history else context
        jung_user += f"\n\n[Round {r}] Generate a candidate proof approach, identify hidden hypotheses, or surface structural invariants. Do NOT close the proof."

        logger.info("Jung round %d/%d ...", r, rounds)
        jung_response = _call_llm(jung_prompt, jung_user, model=model)
        jung_turn = SocraticTurn(round=r, speaker="jung", prompt=jung_user[:500],
                                 response=jung_response)

        # Extract Lean code block if present
        code_match = re.search(r"```(?:lean4|lean)?\s*\n(.*?)```", jung_response, re.DOTALL)
        if code_match:
            jung_turn.lean_code = code_match.group(1).strip()

        result.turns.append(jung_turn)
        dialogue_history.append(f"[JUNG R{r}]: {jung_response[:800]}")

        # --- PAULI TURN: adjudicate ---
        pauli_user = (
            f"THEOREM TARGET: {theorem_target}\n\n"
            f"JUNG'S PROPOSAL (Round {r}):\n{jung_response[:1500]}\n\n"
            f"Apply Pauli adjudication: identify obstructions, missing hypotheses, "
            f"vacuity risks, or circular dependencies. "
            f"Output: PASS (with exact reason) or FAIL (with exact obstruction term)."
        )

        logger.info("Pauli round %d/%d ...", r, rounds)
        pauli_response = _call_llm(pauli_prompt, pauli_user, model=model)
        pauli_turn = SocraticTurn(round=r, speaker="pauli", prompt=pauli_user[:500],
                                  response=pauli_response)

        result.turns.append(pauli_turn)
        dialogue_history.append(f"[PAULI R{r}]: {pauli_response[:800]}")

        # Check for convergence: did Pauli say PASS?
        if re.search(r'\bPASS\b', pauli_response, re.IGNORECASE) and \
           not re.search(r'\bFAIL\b', pauli_response, re.IGNORECASE):
            result.convergence = True
            logger.info("Convergence at round %d", r)
            break

    result.duration_s = time.time() - start
    return result


# ---------------------------------------------------------------------------
# Scoring engine
# ---------------------------------------------------------------------------

def score_dialogue(result: DialogueResult, lean_project: Path) -> DialogueResult:
    """Score a socratic dialogue along multiple dimensions.

    Scoring weights derived from auto/gepa_training_logs.json fitness distribution
    (range 0.5-0.95) and Black Book 18's Jung-Pauli dialectic:
      - Jung contribution: hypothesis surface, translation quality
      - Pauli contribution: obstruction specificity, vacuity detection
      - Vessel (toolchain): compile success, Lean kernel verification
    """
    score = 0.0
    details: list[str] = []

    # 1. Vacuity score (Pauli's core function)
    all_code = "\n".join(t.lean_code for t in result.turns if t.lean_code)
    if all_code:
        result.vacuity_score = _score_vacuity(all_code)
    else:
        result.vacuity_score = 0.5  # no code to evaluate
    score += 0.25 * result.vacuity_score
    details.append(f"vacuity={result.vacuity_score:.2f}")

    # 2. Lean compile check (the vessel)
    if all_code:
        compile_result = _compile_lean(all_code, lean_project)
        result.compile_success = compile_result["success"]
        result.compile_errors = compile_result["stderr"]
        result.lean_file = compile_result["lean_file"]
        if result.compile_success:
            score += 0.35
            details.append("compile=PASS")
        else:
            score += 0.05  # partial credit for producing compilable-ish code
            details.append("compile=FAIL")
    else:
        score += 0.0
        details.append("compile=NO_CODE")

    # 3. Hypothesis surface rate (Jung's core function)
    hypothesis_keywords = ["hypothesis", "assumption", "requires", "depends on",
                           "if and only if", "necessary condition", "sufficient condition"]
    jung_text = " ".join(t.response.lower() for t in result.turns if t.speaker == "jung")
    surfaced = sum(1 for kw in hypothesis_keywords if kw in jung_text)
    result.hypothesis_surface_rate = min(1.0, surfaced / max(1, len(hypothesis_keywords)))
    score += 0.15 * result.hypothesis_surface_rate
    details.append(f"hypothesis_surface={result.hypothesis_surface_rate:.2f}")

    # 4. Obstruction specificity (Pauli's core function)
    pauli_text = " ".join(t.response for t in result.turns if t.speaker == "pauli")
    result.obstruction_specific = bool(
        re.search(r'(?:obstruction|blocker|cannot proceed because|missing):\s*\S', pauli_text, re.IGNORECASE)
    )
    if result.obstruction_specific:
        score += 0.15
        details.append("obstruction=SPECIFIC")
    else:
        details.append("obstruction=VAGUE")

    # 5. Convergence (did they agree?)
    result.convergence = result.convergence or (
        "PASS" in pauli_text.upper() and "FAIL" not in pauli_text.upper()
    )
    if result.convergence:
        score += 0.10
        details.append("convergence=YES")
    else:
        details.append("convergence=NO")

    # Normalize
    result.fitness = min(1.0, max(0.0, score))
    logger.info("Dialogue score: %.3f (%s)", result.fitness, ", ".join(details))
    return result


# ---------------------------------------------------------------------------
# GEPA integration -- dialogue as fitness signal
# ---------------------------------------------------------------------------

@dataclass
class GenerationRecord:
    """One generation of evolved socratic prompts."""
    generation: int
    jung_prompt: str
    pauli_prompt: str
    fitness: float
    dialogue_result: Optional[DialogueResult] = None
    jung_seed_idx: int = -1
    pauli_seed_idx: int = -1
    mutation: str = ""


def evolve_socratic_prompts(
    theorem_target: str,
    theorem_statement: str = "",
    generations: int = 5,
    population_size: int = 8,
    rounds: int = 3,
    model: str = "deepseek-chat",
    lean_project: Optional[Path] = None,
) -> list[GenerationRecord]:
    """Evolve socratic dialogue prompts using GEPA-like genetic search.

    Population: pairs of (jung_prompt, pauli_prompt) from seed pools.
    Fitness: score_dialogue() on the theorem target.
    Selection: top-k pairs survive; mutations applied to produce next generation.
    """
    if lean_project is None:
        lean_project = _REPO

    # Initialize population from seed pools
    population: list[GenerationRecord] = []
    for gen in range(generations):
        logger.info("=== Generation %d/%d ===", gen + 1, generations)
        gen_records: list[GenerationRecord] = []

        for i in range(population_size):
            if gen == 0:
                # First generation: grid over seeds
                ji = i % len(JUNG_SEEDS)
                pi = i % len(PAULI_SEEDS)
                jung = JUNG_SEEDS[ji]
                pauli = PAULI_SEEDS[pi]
                mutation = "seed"
            else:
                # Subsequent generations: mutate top performers
                if population:
                    # Select parent from previous generation (tournament selection)
                    parent = max(population[-population_size:], key=lambda r: r.fitness)
                    jung, pauli = _mutate_prompts(parent.jung_prompt, parent.pauli_prompt, i)
                    ji, pi = parent.jung_seed_idx, parent.pauli_seed_idx
                    mutation = f"mutated_from_gen{gen}"
                else:
                    ji = i % len(JUNG_SEEDS)
                    pi = i % len(PAULI_SEEDS)
                    jung = JUNG_SEEDS[ji]
                    pauli = PAULI_SEEDS[pi]
                    mutation = "fallback_seed"

            # Run socratic dialogue
            logger.info("  Individual %d/%d (jung=%d, pauli=%d, %s)",
                        i + 1, population_size, ji, pi, mutation)
            result = run_socratic_dialogue(
                theorem_target=theorem_target,
                theorem_statement=theorem_statement,
                jung_prompt=jung,
                pauli_prompt=pauli,
                rounds=rounds,
                model=model,
            )

            # Score it
            result = score_dialogue(result, lean_project)

            record = GenerationRecord(
                generation=gen + 1,
                jung_prompt=jung,
                pauli_prompt=pauli,
                fitness=result.fitness,
                dialogue_result=result,
                jung_seed_idx=ji,
                pauli_seed_idx=pi,
                mutation=mutation,
            )
            gen_records.append(record)
            logger.info("    fitness=%.3f  vacuity=%.2f  compile=%s  converge=%s",
                        result.fitness, result.vacuity_score,
                        result.compile_success, result.convergence)

        # Sort by fitness
        gen_records.sort(key=lambda r: r.fitness, reverse=True)
        population.extend(gen_records)

        # Log top performer
        best = gen_records[0]
        logger.info("  Best gen %d: fitness=%.3f (jung_seed=%d, pauli_seed=%d)",
                    gen + 1, best.fitness, best.jung_seed_idx, best.pauli_seed_idx)

    return population


# ---------------------------------------------------------------------------
# Prompt mutation operators (GEPA-like)
# ---------------------------------------------------------------------------

_MUTATIONS = [
    # Add specificity
    lambda p: p + "\n\nAlways cite exact Lean 4 theorem names from mathlib4.",
    lambda p: p + "\n\nIf a hypothesis is missing, name it precisely.",
    lambda p: p + "\n\nPrioritize falsifiability: what would disprove this claim?",
    lambda p: p + "\n\nOutput in sections: [INVARIANT], [OBSTRUCTION], [OPEN QUESTION].",
    # Add constraints
    lambda p: "Be ruthlessly concise. " + p,
    lambda p: "Think in kernel-checkable terms. " + p,
    lambda p: "Assume the codebase uses Lean 4.28.1 with mathlib4. " + p,
    # Role specificity
    lambda p: p.replace("explorer", "structural invariant detector"),
    lambda p: p.replace("adjudicator", "kernel-level obstruction finder"),
    # Style variants
    lambda p: p + "\n\nFormat: [FINDING] → [EVIDENCE] → [RECOMMENDATION].",
    lambda p: p + "\n\nUse bullet points for obstruction terms.",
    # Black Book 18 specific
    lambda p: p + "\n\nRemember: exploration may be Jungian, closure must be Pauli.",
]


def _mutate_prompts(jung: str, pauli: str, seed: int) -> tuple[str, str]:
    """Apply random mutation to prompt pair. Seed determines which mutation."""
    import random
    rng = random.Random(seed)

    # 70% chance: mutate one prompt; 30% chance: mutate both
    if rng.random() < 0.7:
        if rng.random() < 0.5:
            mutation = rng.choice(_MUTATIONS)
            jung = mutation(jung)
        else:
            mutation = rng.choice(_MUTATIONS)
            pauli = mutation(pauli)
    else:
        m1 = rng.choice(_MUTATIONS)
        m2 = rng.choice(_MUTATIONS)
        jung = m1(jung)
        pauli = m2(pauli)

    return jung, pauli


# ---------------------------------------------------------------------------
# Hive queue integration
# ---------------------------------------------------------------------------

def push_to_hive_queue(dialogue_result: DialogueResult, theorem_target: str) -> Optional[str]:
    """Push a scored dialogue result to the Hive ArangoDB queue for further processing."""
    try:
        from tools.infra.arango_env import (
            arango_database, arango_endpoint, arango_password,
            arango_username, load_repo_arango_env,
        )
        from tools.infra.hive_arango_queue import aql

        load_repo_arango_env(_REPO)
        ep = arango_endpoint()
        db = arango_database("hive_live")
        usr = arango_username()
        pwd = arango_password("alexandria_root")

        # Push as a SocraticQuestionPacket
        packet = {
            "kind": "SocraticQuestionPacket",
            "status": "open",
            "authority": "semantic",
            "epistemic_layer": "cognitive_process",
            "authority_origin": "socratic_interrogation",
            "cognitive_function": "thinking",
            "promotion_allowed": False,
            "question": f"Socratic dialogue result for {theorem_target}",
            "question_type": "definition_pressure",
            "target_packet_ids": [theorem_target],
            "missing_hypotheses": [],
            "allowed_uses": ["candidate_refinement"],
            "forbidden_uses": ["proof"],
            "_meta": {
                "fitness": dialogue_result.fitness,
                "vacuity_score": dialogue_result.vacuity_score,
                "compile_success": dialogue_result.compile_success,
                "convergence": dialogue_result.convergence,
                "rounds": len(dialogue_result.turns),
            },
        }

        result = aql(ep, db, usr, pwd, """
            INSERT @packet INTO hive_tasks
            RETURN NEW
        """, bind_vars={"packet": packet})

        if result:
            task_id = result[0].get("_key", "")
            logger.info("Pushed to Hive queue: %s", task_id)
            return task_id
    except Exception as exc:
        logger.warning("Hive queue push failed (non-fatal): %s", exc)

    return None


# ---------------------------------------------------------------------------
# Report generation
# ---------------------------------------------------------------------------

def generate_report(population: list[GenerationRecord], theorem_target: str,
                    output_path: Optional[Path] = None) -> str:
    """Generate a markdown report of the evolution run."""
    lines = [
        f"# Socratic-GEPA Evolution Report",
        f"",
        f"**Theorem target:** `{theorem_target}`",
        f"**Generated:** {datetime.now(timezone.utc).isoformat()}",
        f"**Generations:** {max(r.generation for r in population)}",
        f"**Population size:** {sum(1 for r in population if r.generation == 1)}",
        f"",
        f"## Best Prompts per Generation",
        f"",
    ]

    for gen in sorted(set(r.generation for r in population)):
        gen_records = [r for r in population if r.generation == gen]
        best = max(gen_records, key=lambda r: r.fitness)
        lines.append(f"### Generation {gen} -- fitness {best.fitness:.3f}")
        lines.append(f"")
        lines.append(f"**Jung prompt:**")
        lines.append(f"```")
        lines.append(best.jung_prompt[:500])
        lines.append(f"```")
        lines.append(f"")
        lines.append(f"**Pauli prompt:**")
        lines.append(f"```")
        lines.append(best.pauli_prompt[:500])
        lines.append(f"```")
        lines.append(f"")

        if best.dialogue_result:
            dr = best.dialogue_result
            lines.append(f"| Metric | Value |")
            lines.append(f"|--------|-------|")
            lines.append(f"| Vacuity score | {dr.vacuity_score:.2f} |")
            lines.append(f"| Compile success | {dr.compile_success} |")
            lines.append(f"| Hypothesis surface | {dr.hypothesis_surface_rate:.2f} |")
            lines.append(f"| Obstruction specific | {dr.obstruction_specific} |")
            lines.append(f"| Convergence | {dr.convergence} |")
            lines.append(f"| Duration | {dr.duration_s:.1f}s |")
            lines.append(f"| Turns | {len(dr.turns)} |")
            lines.append(f"")

    # Overall best
    overall_best = max(population, key=lambda r: r.fitness)
    lines.append(f"## Overall Best")
    lines.append(f"Fitness: **{overall_best.fitness:.3f}** (gen {overall_best.generation})")
    lines.append(f"")

    report = "\n".join(lines)
    if output_path:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(report, encoding="utf-8")
        logger.info("Report written to %s", output_path)

    return report


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Socratic-GEPA-Hive Adapter -- adversarial-collaborative proof evolution",
    )
    parser.add_argument("--theorem", required=True,
                        help="Fully qualified theorem name to target")
    parser.add_argument("--statement", default="",
                        help="Optional theorem statement (natural language)")
    parser.add_argument("--generations", type=int, default=5,
                        help="Number of GEPA generations")
    parser.add_argument("--population", type=int, default=8,
                        help="Population size per generation")
    parser.add_argument("--rounds", type=int, default=3,
                        help="Socratic dialogue rounds per individual")
    parser.add_argument("--model", default="deepseek-chat",
                        help="LLM model for dialogue")
    parser.add_argument("--lean-project", type=Path, default=_REPO,
                        help="Path to Lean 4 project root")
    parser.add_argument("--output", type=Path, default=None,
                        help="Path for markdown report")
    parser.add_argument("--push-hive", action="store_true",
                        help="Push best result to Hive ArangoDB queue")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print what would run without making API calls")
    parser.add_argument("--verbose", action="store_true",
                        help="Verbose logging")

    args = parser.parse_args()

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)s [%(name)s] %(message)s",
    )

    if args.dry_run:
        logger.info("DRY RUN -- would evolve socratic prompts for: %s", args.theorem)
        logger.info("  Generations: %d, population: %d, rounds: %d",
                    args.generations, args.population, args.rounds)
        logger.info("  Model: %s, lean-project: %s", args.model, args.lean_project)
        logger.info("  Seed Jung prompts: %d, Pauli prompts: %d",
                    len(JUNG_SEEDS), len(PAULI_SEEDS))
        return

    # Run evolution
    population = evolve_socratic_prompts(
        theorem_target=args.theorem,
        theorem_statement=args.statement,
        generations=args.generations,
        population_size=args.population,
        rounds=args.rounds,
        model=args.model,
        lean_project=args.lean_project,
    )

    # Generate report
    output_path = args.output or (_REPO / "artifacts" / "socratic_gepa" /
                                   f"{args.theorem.replace('.', '_')}_{int(time.time())}.md")
    report = generate_report(population, args.theorem, output_path)
    print(report[:2000])

    # Push best to Hive
    if args.push_hive:
        best = max(population, key=lambda r: r.fitness)
        if best.dialogue_result:
            task_id = push_to_hive_queue(best.dialogue_result, args.theorem)
            if task_id:
                print(f"\nPushed to Hive: {task_id}")

    # Print summary
    best_overall = max(population, key=lambda r: r.fitness)
    print(f"\nBest fitness: {best_overall.fitness:.3f} (gen {best_overall.generation})")
    print(f"Total dialogues: {len(population)}")
    print(f"Report: {output_path}")


if __name__ == "__main__":
    main()
