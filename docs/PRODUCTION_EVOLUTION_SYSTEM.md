# Production Evolution System

## Architecture

A self-evolving autonomous pipeline that eliminates `_True : Prop := by` certificate debt across 121+ Lean 4 files. The system runs as a systemd daemon, processes tasks from an ArangoDB queue, evolves skills via GEPA/DSPy genetic optimization, and closes proof debt through a multi-stage audit pipeline.

```
┌─────────────────────────────────────────────────────────────────┐
│                    EVOLUTION LOOP                                │
│                                                                 │
│  ArangoDB Queue ──→ GEPA/DSPy (evolves skill)                  │
│       │                    │                                    │
│       │              ┌─────▼──────┐                             │
│       │              │ RealEvaluator│  Hermes runs on real       │
│       │              │   runs tasks │  _True fields              │
│       │              └─────┬──────┘                             │
│       │                    │                                    │
│       │              ┌─────▼──────┐                             │
│       │              │ Pareto     │  Score → selection          │
│       │              │ selection  │                              │
│       │              └─────┬──────┘                             │
│       │                    │                                    │
│       │              Failed tasks                               │
│       │                    │                                    │
│       │       ┌────────────▼──────────────┐                     │
│       │       │   Three-Stage Prover      │                     │
│       │       │                           │                     │
│       │       │  0. ChatGPT audit (CDP)   │  Browser-harness     │
│       │       │  1. Pi/DeepSeek generate  │  Coding agent       │
│       │       │  2. arXiv search/retry    │  Literature          │
│       │       └────────────┬──────────────┘                     │
│       │                    │                                    │
│       │              ┌─────▼──────┐                             │
│       │              │ Vacuity    │  Discovers new obfuscation  │
│       │              │ Critic     │  synonym patterns           │
│       │              └─────┬──────┘                             │
│       │                    │                                    │
│       │              ┌─────▼──────┐                             │
│       │              │ Archive    │  Saves evolved skill        │
│       │              │ + Codex    │  with fitness score         │
│       │              └────────────┘                             │
│       │                    │                                    │
│       └────────────────────┘  Skill improves with each gen      │
└─────────────────────────────────────────────────────────────────┘
```

## Agent Roles

### GEPA/DSPy — Genetic Optimizer
- **Module**: `tools/infra/gepa_evolver.py`
- **Engine**: `dspy.GEPA` (Pareto-optimal genetic prompt search)
- **Mutates**: skill files (SKILL.md) as evolvable parameters
- **Selects**: best performer via Pareto front (fitness + size)

### RealEvaluator — Ground Truth Gate
- **Module**: `tools/infra/gepa_real_eval.py`
- **Invokes**: Hermes or Pi against real `_True : Prop := by` fields
- **Checks**: `sorry` removal + Lean compilation (`lake env lean`)
- **Caches**: evaluation results with file hash for dedup
- **Restores**: original file after evaluation

### Three-Stage Prover — Debt Closure
- **Module**: `tools/infra/proof_seeker.py`

**Stage 0: ChatGPT Audit (Browser CDP)**
- Sends full file context to ChatGPT via `browser-harness` (Chrome DevTools Protocol)
- Uses `innerText` on `<pre><code>` DOM for formatted code extraction
- Stability polling: waits for response to finish streaming
- Saves to file → compiles → sends errors back for fix (2 retries)
- The same ChatGPT tab preserves context across calls

**Stage 1: Pi/DeepSeek Coding Agent**
- Lightweight coding agent (`pi --provider deepseek --model deepseek-v4-flash`)
- Loads `audit-proof` and `closure-debt-proof` skills as methodology
- Iterative fix loop: write → compile → read errors → fix → repeat (3 attempts)

**Stage 2: arXiv Literature Search**
- Searches arXiv, mathlib (LeanSearch/Loogle), Alexandria corpus
- Re-digests found papers into candidate proofs
- Used as escalation when stages 0-1 fail

### Vacuity Critic — Pattern Discovery
- **Module**: `tools/infra/vacuity_critic.py`
- Reviews failed evaluations to discover new obfuscation synonym patterns
- Expands the detection dictionary in `skills/closure-debt-proof/SKILL.md`
- Generates candidates from the LLM's latent associations
- Currently tracks: `_True`, `_sorryProof`, `_certificate`, `_valid`, `_witness`, `_bridge`, `_surety`, `_indemnity`, `_attestation`, `_covenant`, `_verity`, `_testimony`, `_accreditation`, `_bond`, `_seal`, `_voucher`, `_nexus`, `_guaranty`

### Evolution Worker — Autonomous Daemon
- **Module**: `tools/infra/evolution_worker.py`
- **Service**: `systemd` (evolution-worker.service)
- **Poll interval**: 5 seconds
- **Skill type**: `skill-evolution` queue in ArangoDB
- Processes: GEPA evolve → evaluate → prove (3-stage) → critique → archive → repeat

## Operational Commands

## System Management
```bash
# View worker status
systemctl status evolution-worker
journalctl -u evolution-worker -f

# Restart (after code changes)
sudo systemctl restart evolution-worker

# Run one cycle manually
python3 tools/infra/evolution_worker.py --once
```

### Queue Operations
```bash
# Enqueue an evolution task
python3 tools/infra/evolution_worker.py --enqueue audit-proof 10

# Enqueue closure-debt task
python3 tools/infra/evolution_worker.py --enqueue closure-debt-proof 5

# Check queue state
python3 -c "
from tools.infra.hive_arango_queue import queue_stats
from tools.infra.arango_env import *
from pathlib import Path; load_repo_arango_env(Path.cwd())
for q in ['proof-search', 'skill-evolution']:
    s = queue_stats(*args, queue_name=q)
    print(f'{q}:', {r['status']: r['count'] for r in s['rows']})
"
```

### ChatGPT Audit (Manual)
```bash
# Start Chrome with remote debugging
chromium --remote-debugging-port=9222 &

# Run audit (thinking mode, same tab)
browser-harness -c "exec(open('tmp/browser-harness/run_audit.py').read()); print(run_audit(open('prompt.txt').read(), timeout=90))"

# Run with Extended Pro (manual model selection)
browser-harness -c "exec(open('tmp/browser-harness/audit_verified.py').read())"
```

### Proof Seeker Manual
```bash
# Search for existing proofs
python3 tools/infra/proof_seeker.py --target "tri_facet_sum_id" --search-only

# Full pipeline (search + digest + formalize)
python3 tools/infra/proof_seeker.py \
  --target "jones_eq_coeff_projector_sum" \
  --context-file lean/InfoGeometry/OperatorAlgebra/JonesCalibration.lean \
  --formalize --line 350
```

### Dictionary Expansion
```bash
# Discover new obfuscation patterns
python3 tools/infra/vacuity_critic.py --expand-dictionary

# Scan a file for known patterns
python3 tools/infra/vacuity_critic.py --scan-file lean/InfoGeometry/OperatorAlgebra/JonesCalibration.lean
```

## Configuration Files

| File | Purpose |
|---|---|
| `tools/infra/hermes_config.yaml` | Hermes provider routing (DeepSeek, fallbacks) |
| `tools/infra/evolution-worker.service` | systemd daemon definition |
| `~/.hermes/.env` | API keys (DEEPSEEK_API_KEY, OPENROUTER_API_KEY) |
| `~/.hermes/config.yaml` | Hermes model config (deepseek-v4-flash) |
| `tools/schema/vacuity/certificate_patterns.json` | Obfuscation detection schema |
| `quarantine/hermes_skills/archive/*/manifest.jsonl` | Evolution lineage |

## Skills

| Skill | Purpose | Status |
|---|---|---|
| `audit-proof` | Audit persona — BUCKET classification, zero prose | Active |
| `closure-debt-proof` | Eliminate `_True`/`_sorryProof` patterns | Active |
| `lean-proof` | General Lean proof methodology | Archived |

## Codex

The Codex (`docs/codex/codex.md`) defines what IS and what is WRONG in mathematical formalization:
- **BUCKET 1**: Kernel-checked theorems with zero dependencies
- **BUCKET 2**: Conditional theorems from explicit witnesses
- **BUCKET 3**: Open closure debt — identified, named, tracked

Every file added to the codebase must carry the audit protocol map.

## Production Files (BUCKET 1 — Verified Compile)

| File | Theorems | Domain |
|---|---|---|
| `TriFacetGeometry.lean` | 8 | Scalar tri-facet projector algebra |
| `TriFacetEigenspace.lean` | 4 | Eigenspace + spectral reconstruction |
| `HodgeKreinTriFacet.lean` | 12 | Linear Hodge-Krein decomposition |
| `GoldenRatioInvariants.lean` | 9 | Fibonacci/Verlinde fusion algebra |
| `GrothendieckGroup.lean` | 20+ | K₀(Spec F) ≅ ℤ |
| `K0Functor.lean` | 9 | Functorial K0 completion |
| `JonesCalibration.lean` | 25+ | Jones optical calibration (ChatGPT-generated) |
| `AxiomaticDependencyGraph.lean` | 16 | Node 0→5 architecture |
| `KeywordIndex.lean` | 3 | 13-domain formal catalog |
