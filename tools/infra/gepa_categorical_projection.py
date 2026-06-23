#!/usr/bin/env python3
"""
GEPA adapter for categorical-infrastructure-projection skill.

Leverages CPU multiprocessing (parallel lake build) and GPU batch inference
(DSPy/LLM proof generation) on multiprocessor GPU systems.

Genome:
    - carrier, matrix, functor, bilingual_key
    - proof_strategy: composable strategy string
    - fitness: -1 (fail), 0 (untested), 1 (builds), 2 (closed)

Usage:
    # Target the Yang-Baxter proof file and evolve against its Lean errors
    python3 tools/infra/gepa_categorical_projection.py --evolve --generations 10 \
        --task yang_baxter_braid_relation \
        --target-file lean/InfoGeometry/Canonical/YangBaxterProof.lean

    # CPU-parallel evaluation (default)
    python3 tools/infra/gepa_categorical_projection.py --evolve --generations 10 --workers 8

    # GPU batch inference (requires DSPy + CUDA)
    python3 tools/infra/gepa_categorical_projection.py --evolve --gpu --generations 20
"""

import concurrent.futures
import json
import os
import random
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[2]
LAKE = shutil.which("lake") or "lake"
N_CPU = os.cpu_count() or 1
DEFAULT_TARGET_FILE = Path(
    os.environ.get(
        "GEPA_TARGET_FILE",
        "lean/InfoGeometry/Canonical/YangBaxterProof.lean",
    )
)
DEFAULT_BUILD_TARGET = os.environ.get("GEPA_BUILD_TARGET", "")

YANG_BAXTER_ERROR_SURFACE = [
    "braid_relation entry proof rewrites q^6/q^7/q^8/q^9 before the goal exposes powers",
    "h_s_sq calc parses the final equality as the wrong calc step type",
    "entrywise matrix-vector normal forms remain after simp and ring",
    "the proof should specialize a generic diagonal Artin relation over C",
    "the scalar side condition is a cyclotomic linear_combination of q^4 - q^3 + q^2 - q + 1",
]

# ── DSPy GPU inference (optional) ──────────────────────────────────────────

try:
    import dspy
    HAS_DSPY = True
except ImportError:
    HAS_DSPY = False

# ── Genome definition ──────────────────────────────────────────────────────

STRATEGIES = [
    "rotor_mul",
    "nilpotent_expansion",
    "F_diagonalization",
    "colimit_cone",
    "direct_2x2",
    "complex_diagonal_artin",
    "cyclotomic_linear_combination",
    "zpow_diagonal_specialization",
    "bilingual_translation",
    "characteristic_polynomial",
]

GENOMES = [
    {
        "task_id": "yang_baxter_braid_relation",
        "target_file": "lean/InfoGeometry/Canonical/YangBaxterProof.lean",
        "target_decl": "InfoGeometry.Canonical.YangBaxterProof.braid_relation",
        "carrier": "two_channel_fibonacci_braid",
        "matrix": "R * B * R = B * R * B",
        "category": "Canonical.FibonacciBraiding",
        "functor": "complex diagonal Artin specialization",
        "bilingual_key": "tau_eq_q_minus_q4_minus_one + cyclotomic_relation",
        "proof_strategy": "complex_diagonal_artin + cyclotomic_linear_combination + zpow_diagonal_specialization",
        "error_surface": YANG_BAXTER_ERROR_SURFACE,
        "fitness": 0.0,
        "status": "open",
    },
    {
        "task_id": "monodromy_power_binomial",
        "carrier": "monodromyCarrier",
        "matrix": "hadjiivanovMonodromy h",
        "category": "RealKVect",
        "functor": "complexToRealK",
        "bilingual_key": "realPhaseAxis_eq_complex_i",
        "proof_strategy": "rotor_mul + nilpotent_binomial_expansion",
        "fitness": 0.0,
        "status": "open",
    },
    {
        "task_id": "monodromy_F_diagonalization",
        "carrier": "monodromyCarrier",
        "matrix": "hadjiivanovMonodromy h",
        "category": "RealKVect",
        "functor": "complexToRealK",
        "bilingual_key": "realPhaseAxis_eq_complex_i",
        "proof_strategy": "F_diagonalization",
        "fitness": 0.0,
        "status": "open",
    },
    {
        "task_id": "braid_hecke_form",
        "carrier": "monodromyCarrier",
        "matrix": "fibonacciBMatrix q τ s",
        "category": "RealKVect",
        "functor": "complexToRealK",
        "bilingual_key": "realPhaseAxis_eq_complex_i",
        "proof_strategy": "direct_2x2",
        "fitness": 0.0,
        "status": "open",
    },
    {
        "task_id": "cantor_representation",
        "target_file": "lean/InfoGeometry/Canonical/JordanWignerCantorRepresentation.lean",
        "target_decl": "InfoGeometry.Canonical.JordanWignerCantorRepresentation.buildCantorRep_one_is_jw_rep",
        "carrier": "MatStage 1",
        "matrix": "complexifyMat 1 (jwCreation 1 0)",
        "category": "CantorOp 1",
        "functor": "Matrix.toLin",
        "bilingual_key": "idxEquivCantorAddress",
        "proof_strategy": "direct_2x2",
        "error_surface": [],
        "fitness": 0.0,
        "status": "open",
    },
]


# ── GPU batch proof generation (DSPy) ─────────────────────────────────────

def dspy_lm():
    """Configure DSPy with GPU-accelerated LM if available."""
    if not HAS_DSPY:
        return None
    # Prefer local GPU model (vLLM / llama.cpp with CUDA)
    if os.environ.get("GEPA_LM"):
        model = os.environ["GEPA_LM"]
    else:
        model = "openai/gpt-4o-mini"  # fallback
    return dspy.LM(model=model, cache=False)


def gpu_batch_generate(genomes: list[dict]) -> list[str]:
    """Generate candidate proof completions on GPU in a single batch.

    Uses DSPy to fill the `:= by sorry` block for each genome.
    The batch runs on GPU (CUDA) via the LM backend.
    """
    lm = dspy_lm()
    if lm is None:
        return [""] * len(genomes)

    dspy.settings.configure(lm=lm)

    prompt_tmpl = """\
You are projecting categorical infrastructure onto a concrete matrix computation.

Task: {task_id}
Target file: {target_file}
Target declaration: {target_decl}
Carrier: {carrier}
Matrix: {matrix}
Category: {category}
Functor: {functor}
Bilingual key: {bilingual_key}
Strategy: {proof_strategy}
Observed Lean errors / failure surface:
{error_surface}

Write the Lean 4 proof body (the block after `:= by`) that closes this theorem.
The proof must use only:
- rotor_mul, nilpotent_binomial_expansion (if strategy includes these)
- diagonal Artin specialization and cyclotomic linear_combination (for Yang-Baxter tasks)
- Fmatrix_asRealK, hadjiivanovMonodromy_asRealK
- LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply
- ring, simp, ext, calc

Output ONLY the proof block (no markdown, no commentary)."""

    batch = []
    for g in genomes:
        prompt_data = dict(g)
        prompt_data.setdefault("target_file", str(DEFAULT_TARGET_FILE))
        prompt_data.setdefault("target_decl", "")
        prompt_data.setdefault("error_surface", "")
        batch.append(prompt_tmpl.format(**prompt_data))

    # GPU batch inference
    responses = lm(messages=[{"role": "user", "content": p} for p in batch],
                   temperature=0.3, max_tokens=500)
    return [r.choices[0].message.content if hasattr(r, 'choices') else str(r)
            for r in responses]


# ── CPU-parallel fitness evaluation ────────────────────────────────────────

BUILD_TARGET = DEFAULT_BUILD_TARGET or "InfoGeometry.Quantum.RealKCategory"


def _target_command(
    target_file: str | Path | None = None,
    build_target: str | None = None,
) -> list[str]:
    if target_file:
        return [LAKE, "env", "lean", str(target_file)]
    return [LAKE, "build", build_target or BUILD_TARGET]


def _error_excerpt(stderr: str, max_lines: int = 20) -> str:
    lines = [line for line in stderr.splitlines() if "error:" in line or "unsolved goals" in line]
    return "\n".join(lines[:max_lines])


def _eval_one(genome: dict[str, Any], timeout_s: int = 120) -> dict[str, Any]:
    """Evaluate one genome: lake build, check for sorry."""
    t0 = time.time()
    target_file = genome.get("target_file") or None
    build_target = genome.get("build_target") or BUILD_TARGET
    result = subprocess.run(
        _target_command(target_file, build_target),
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=timeout_s,
    )
    build_ok = result.returncode == 0
    elapsed = time.time() - t0

    if not build_ok:
        return {
            "fitness": -1.0,
            "elapsed_s": elapsed,
            "error_excerpt": _error_excerpt(result.stderr),
        }

    score = 1.0
    target_path = REPO / str(target_file) if target_file else None
    if target_path and target_path.exists() and "sorry" not in target_path.read_text(encoding="utf-8"):
        score = 2.0
    return {"fitness": score, "elapsed_s": elapsed, "error_excerpt": ""}


def evaluate_population_parallel(genomes: list[dict],
                                  workers: int = N_CPU) -> list[dict]:
    """Evaluate all genomes in parallel using CPU multiprocessing."""
    with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as pool:
        fut_to_idx = {}
        for i, g in enumerate(genomes):
            fut = pool.submit(_eval_one, g)
            fut_to_idx[fut] = i

        for fut in concurrent.futures.as_completed(fut_to_idx):
            i = fut_to_idx[fut]
            try:
                outcome = fut.result()
            except Exception as e:
                print(f"  {genomes[i]['task_id']}: worker error {e}", file=sys.stderr)
                outcome = {"fitness": -1.0, "elapsed_s": 0.0, "error_excerpt": str(e)}
            score = float(outcome.get("fitness", -1.0))
            genomes[i]["fitness"] = score
            genomes[i]["last_eval"] = outcome
            if score >= 1.0:
                genomes[i]["status"] = "builds"
            elif score < 0:
                genomes[i]["status"] = "fails"
            else:
                genomes[i]["status"] = "open"
    return genomes


# ── Evolution loop ─────────────────────────────────────────────────────────

def mutate_strategy(original: str) -> str:
    parts = original.split(" + ")
    if random.random() < 0.3:
        parts.append(random.choice(STRATEGIES))
    if random.random() < 0.3 and len(parts) > 1:
        parts.pop(random.randint(0, len(parts) - 1))
    if random.random() < 0.4:
        idx = random.randint(0, len(parts) - 1)
        parts[idx] = random.choice(STRATEGIES)
    return " + ".join(sorted(set(parts)))


def evolve(generations: int = 10,
           population: list[dict] | None = None,
           workers: int = N_CPU,
           use_gpu: bool = False) -> list[dict]:
    pop = population or [dict(g) for g in GENOMES]

    for gen in range(generations):
        t_gen = time.time()
        print(f"\n=== Generation {gen} ===", file=sys.stderr)

        # Parallel fitness evaluation across all CPU cores
        pop = evaluate_population_parallel(pop, workers=workers)

        # Optionally use GPU batch inference to generate new candidates
        if use_gpu and HAS_DSPY and gen % 2 == 0:
            print("  Running GPU batch inference for new candidates...",
                  file=sys.stderr)
            candidate_bodies = gpu_batch_generate(pop)
            for i, g in enumerate(pop):
                if candidate_bodies[i]:
                    g["_gpu_candidate"] = candidate_bodies[i]

        # Report
        for g in pop:
            icon = {1.0: " ✅", -1.0: " ❌"}.get(g["fitness"], " ⏳")
            print(f"  {g['task_id']}: [{g['proof_strategy']}] "
                  f"fitness={g['fitness']:.1f}{icon}", file=sys.stderr)

        # Selection + mutation
        next_pop = []
        for g in pop:
            if g["fitness"] >= 1.0:
                next_pop.append(g)
            else:
                m = dict(g)
                m["proof_strategy"] = mutate_strategy(g["proof_strategy"])
                m["fitness"] = 0.0
                m["status"] = "mutated"
                next_pop.append(m)
        pop = next_pop

        elapsed = time.time() - t_gen
        builds = sum(1 for g in pop if g["fitness"] >= 1.0)
        print(f"  [{elapsed:.1f}s] builds={builds}/{len(pop)}",
              file=sys.stderr)

    return pop


def main():
    import argparse
    import shutil

    parser = argparse.ArgumentParser(
        description="GEPA adapter (CPU-parallel + GPU batch)")
    parser.add_argument("--evolve", action="store_true")
    parser.add_argument("--generations", type=int, default=10)
    parser.add_argument("--workers", type=int, default=N_CPU // 2,
                        help="Parallel CPU workers for lake build")
    parser.add_argument("--gpu", action="store_true",
                        help="Enable GPU batch inference for proof generation")
    parser.add_argument("--task", action="append", default=[],
                        help="Task id to evolve; repeatable. Defaults to all genomes.")
    parser.add_argument("--target-file", type=Path, default=None,
                        help="Lean file checked by `lake env lean` during fitness evaluation")
    parser.add_argument("--build-target", default=DEFAULT_BUILD_TARGET,
                        help="Optional Lake target used when no --target-file is provided")
    parser.add_argument("--output", type=Path,
                        default=REPO / "quarantine" / "gepa_population.json")
    args = parser.parse_args()

    if args.evolve:
        print(f"CPU workers: {args.workers} "
              f"| target: {args.target_file or args.build_target or 'per-genome'} "
              f"| GPU batch: {'on' if args.gpu else 'off'} "
              f"| DSPy: {'available' if HAS_DSPY else 'not installed'}",
              file=sys.stderr)

        selected_tasks = set(args.task)
        population = [
            dict(genome)
            for genome in GENOMES
            if not selected_tasks or genome["task_id"] in selected_tasks
        ]
        if selected_tasks and not population:
            raise SystemExit(f"no matching GEPA task(s): {', '.join(sorted(selected_tasks))}")

        for genome in population:
            if args.target_file:
                genome["target_file"] = str(args.target_file)
            if args.build_target:
                genome["build_target"] = args.build_target

        final_pop = evolve(generations=args.generations,
                           population=population,
                           workers=args.workers,
                           use_gpu=args.gpu)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with open(args.output, "w") as f:
            json.dump(final_pop, f, indent=2)
        print(f"\nSaved to {args.output}", file=sys.stderr)

        builds = sum(1 for g in final_pop if g["fitness"] >= 1.0)
        print(f"Builds: {builds}/{len(final_pop)}", file=sys.stderr)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
