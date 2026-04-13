# DGX Spark Autonomous Prover Stack (Hermes + NemoClaw + OpenClaw + Lean4)

This guide sets up the autonomous prover stack on **NVIDIA DGX Spark** using the repository's current dual-loop architecture (explore/lock), with:

- `Hermes` as orchestrator shell (not authority surface)
- `NemoClaw` for sandboxed assistant runtime
- `OpenClaw` for skills + memory + gateway control
- `ClawCode`/Lean tooling for closure and diagnostics
- Lean4 prover models (DeepSeek-Prover, InternLM Step-Prover, LeanDojo/ReProver, LeanCopilot)

## 1. Architecture Mapping (Repo-Native)

Use the existing repo lane, not a parallel architecture:

- Policy and handover: `docs/AGENTIC_HANDOVER_POLICY.md`, `docs/CARETAKER_REQUIREMENTS.md`
- Translation roadmap: `docs/black_books/55_external_approval_real_all_translation.md`
- Runtime configs already in repo:
  - `nemoclaw_config.yaml`
  - `tools/infra/hermes_config.yaml`

The repo-native `hermes_config.yaml` already isolates learnable assets to:

- `./quarantine/hermes_skills`
- `./quarantine/hermes_memory`

This keeps Hermes learnable while preserving Lean + canonical files as authority surfaces.

## 2. DGX Spark Baseline (Hardware/Runtime)

From NVIDIA's DGX Spark OpenShell guide:

- DGX Spark with **128GB unified memory**
- At least ~70GB free memory for large local models (or ~25GB for smaller)
- Docker running
- Python 3.12+
- `uv`
- Ollama 0.17+

Reference: `build.nvidia.com/spark/openshell`.

## 3. Install OpenClaw and NemoClaw

### OpenClaw

Recommended install:

```bash
curl -fsSL https://openclaw.ai/install.sh | bash
openclaw onboard --install-daemon
openclaw --version
openclaw doctor
openclaw gateway status
```

OpenClaw skills are AgentSkills-compatible `SKILL.md` folders. Locations/precedence are documented in OpenClaw Skills docs.

### NemoClaw

Quickstart installer:

```bash
curl -fsSL https://www.nvidia.com/nemoclaw.sh | bash
```

Then onboard/connect:

```bash
nemoclaw my-assistant status
nemoclaw my-assistant connect
```

NemoClaw docs explicitly list **DGX Spark + Docker** as tested in quickstart.

## 4. Configure Hermes as Orchestrator (Learnable Skills + Memory)

Use the repo file `tools/infra/hermes_config.yaml`.

Minimal expected shape:

```yaml
model:
  provider: custom
  base_url: http://localhost:11434/v1
  api_key: ollama
  default: hermes-3-llama-3.1-8b
paths:
  skills: ./quarantine/hermes_skills
  memory: ./quarantine/hermes_memory
runtime:
  statement_lock: true
  audit_required: true
```

Create local learnable lanes:

```bash
mkdir -p quarantine/hermes_skills quarantine/hermes_memory
[ -f quarantine/hermes_memory/MEMORY.md ] || printf "# Hermes Memory\n" > quarantine/hermes_memory/MEMORY.md
```

## 5. NIM + NVIDIA Inference Layer

NIM prerequisites include Linux, NVIDIA GPU, supported driver/toolkit, Docker, container toolkit, and NGC API key.

Typical flow:

```bash
export NGC_API_KEY=<your_key>
echo "$NGC_API_KEY" | docker login nvcr.io --username '$oauthtoken' --password-stdin
```

NIM docs also support serving fine-tuned/local HuggingFace checkpoints via environment variables like `NIM_FT_MODEL` or `NIM_MODEL_NAME` depending on container mode.

## 6. Lean4 Toolchain + Prover Layer

### Lean4 base

```bash
sudo apt install -y git curl
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
```

### LeanDojo / ReProver / LeanCopilot

- LeanDojo supports Lean3/Lean4 data extraction and programmatic interaction.
- ReProver main branch is Lean4-only and publishes Lean4 ByT5 prover/retriever models.
- LeanCopilot runs LLM-assisted tactics/proof search inside Lean and supports local (GPU/non-GPU) and remote models.

## 7. Lean4 Pretrained Prover Models (DGX/NVIDIA GPU-friendly)

### Lean-specific theorem-prover models

1. `deepseek-ai/DeepSeek-Prover-V1.5-*` (Lean4-focused; model card cites miniF2F/ProofNet)
2. `internlm/internlm2_5-step-prover` (Lean4 step prover; model card includes miniF2F/ProofNet/Putnam)
3. `kaiyuy/leandojo-lean4-*` (ReProver/LeanDojo ByT5 tactic/retriever models)
4. LeanCopilot built-in model pipeline (`lake exe LeanCopilot/download`)

### Important deployment note

As of the referenced model cards/docs:

- DeepSeek-Prover/InternLM step-prover are published on HuggingFace but are typically **self-served** (e.g., vLLM/TGI/custom server) rather than first-class NIM entries.
- NIM LLM catalog is broad (DeepSeek, Llama, etc.), but Lean-specific prover models are generally integrated as custom local model serving behind OpenAI-compatible endpoints.

## 8. OpenClaw Memory/Skills Integration for Proving

OpenClaw memory files (workspace-local):

- `MEMORY.md`
- `memory/YYYY-MM-DD.md`
- optional `DREAMS.md`

OpenClaw skills install/update:

```bash
openclaw skills install <skill-slug>
openclaw skills update --all
```

Recommended for prover stack:

- keep Lean automation skills in workspace `skills/`
- keep Hermes adaptive skills in `quarantine/hermes_skills`
- use explicit promotion to canonical repo skills only after proof-carrying validation

## 9. ChatGPT History Import (OpenClaw v2026.4.11+)

OpenClaw added ChatGPT import ingestion in `v2026.4.11` (and it is present in `v2026.4.12`).
This is the highest-impact path if you have GB-scale prior theory chats.

### Version gate

```bash
openclaw --version
# expect >= 2026.4.11
```

### Enable/prepare memory-wiki

```bash
openclaw wiki status
openclaw wiki init
openclaw wiki doctor
```

### Import flow (CLI-first)

The memory-wiki plugin exposes ChatGPT import support in the `wiki` CLI surface.
Check exact subcommands on your installed version:

```bash
openclaw wiki --help
openclaw wiki chatgpt --help
```

Typical import/maintenance flow:

```bash
# import from your ChatGPT export artifact(s)
openclaw wiki chatgpt import <chatgpt-export-path>

# rebuild compiled digests and dashboards
openclaw wiki compile
openclaw wiki lint

# inspect imported material
openclaw wiki search "modular supercharge"
openclaw wiki get <page-or-claim-id>
```

Rollback support is also available in the ChatGPT import lane:

```bash
openclaw wiki chatgpt rollback <run-id>
```

### UI verification

In Dreaming, verify the new subtabs:

- `Imported Insights`
- `Memory Palace`

These surfaces were added with the ChatGPT import feature and are intended for source-chat inspection plus compiled-memory review.

### Large dataset guidance (GB-scale)

- Import in batches (per export file/date range), then `compile`/`lint` after each batch.
- Keep `maxConcurrentJobs` conservative in `memory-wiki` config on first run.
- Prefer `bridge` mode for safe ingestion from public memory artifacts.
- Always run `wiki lint` before trusting derived claims for theorem-target packets.

## 10. Locked Diagnostics (No Unlocked Submission)

Always run closure builds with the repo lock wrapper to avoid race conditions:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.ProjectorEquivariance \
  InfoGeometry.Dynamics.UnruhKMS \
  InfoGeometry.Canonical.ModularSuperchargeClosure
```

Capture logs before push:

```bash
mkdir -p logs
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.All \
  | tee logs/locked_build_$(date -u +%Y%m%dT%H%M%SZ).log
```

### Runtime lock artifact (required for reproducibility)

The bootstrap script now emits a machine-readable lock file:

- `logs/hermes_runtime_lock_<timestamp>.json`

It records:

- exact toolchain/runtime versions (`openclaw`, `nemoclaw`, `lean`, `lake`, `python`, `docker`, `ollama`)
- git branch + commit head
- configured model endpoints/models (Hermes + discovery + logic engines)
- locked build modules, verdict, and log path

Promotion rule:

- no promotion from quarantine to canonical lanes without a successful locked build and corresponding runtime lock artifact.

## 11. Example Bootstrap Script

See:

- `scripts/setup_dgx_spark_hermes_orchestrator.sh`

It provisions OpenClaw + NemoClaw, initializes Hermes learnable paths, and runs locked diagnostics.

## References

- OpenClaw install docs: https://docs.openclaw.ai/install
- OpenClaw skills docs: https://docs.openclaw.ai/tools/skills
- OpenClaw memory docs: https://docs.openclaw.ai/concepts/memory
- OpenClaw memory-wiki docs: https://docs.openclaw.ai/plugins/memory-wiki
- OpenClaw wiki CLI docs: https://docs.openclaw.ai/cli/wiki
- OpenClaw AGENTS default template: https://docs.openclaw.ai/reference/AGENTS.default
- OpenClaw v2026.4.11 release notes (ChatGPT import ingestion): https://github.com/openclaw/openclaw/releases/tag/v2026.4.11
- OpenClaw v2026.4.12 release notes: https://github.com/openclaw/openclaw/releases/tag/v2026.4.12
- OpenClaw PR #64505 (`Imported Insights` / `Memory Palace`): https://github.com/openclaw/openclaw/pull/64505
- NemoClaw quickstart: https://docs.nvidia.com/nemoclaw/latest/get-started/quickstart.html
- NemoClaw docs index: https://docs.nvidia.com/nemoclaw/index.html
- DGX Spark + OpenShell guide: https://build.nvidia.com/spark/openshell
- NIM get started/prereqs (NVIDIA docs): https://docs.nvidia.com/nim/vision-language-models/1.7.0/getting-started.html
- NIM LLM model catalog: https://docs.nvidia.com/nim/large-language-models/1.10.0/models.html
- NIM fine-tuned/local model serving: https://docs.nvidia.com/nim/large-language-models/1.14.0/ft-support.html
- NeMo Framework docs: https://docs.nvidia.com/nemo-framework/user-guide/25.11/nemotoolkit/index.html
- Lean install (official): https://lean-lang.org/install/manual/
- LeanDojo docs: https://leandojo.readthedocs.io/en/latest/
- ReProver repo: https://github.com/lean-dojo/ReProver
- LeanCopilot repo: https://github.com/lean-dojo/LeanCopilot
- DeepSeek-Prover model card: https://huggingface.co/deepseek-ai/DeepSeek-Prover-V1.5-SFT
- InternLM2.5-Step-Prover model card: https://huggingface.co/internlm/internlm2_5-step-prover
