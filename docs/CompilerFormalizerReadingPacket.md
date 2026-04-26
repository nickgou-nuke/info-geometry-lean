# Compiler/Formalizer Reading Packet

This is the compact entry surface for compiler, formalizer, and repair agents
working across Lean 4, LaTeX, Python/SymPy, Alexandria, and the Hive.

## Read Order

1. [README.md](../README.md)
   - repository authority split, representation-depth spine, and proof-first workflow
2. [docs/LOCAL_TOOLCHAIN_ARCHITECTURE.md](LOCAL_TOOLCHAIN_ARCHITECTURE.md)
   - local Lean/DAG/Arango/LeanTrail execution topology
3. [docs/alexandria/README.md](alexandria/README.md)
   - Alexandria source formats, provenance, coverage, and retrieval artifacts
4. [docs/alexandria/HYBRID_GRAPHRAG.md](alexandria/HYBRID_GRAPHRAG.md)
   - LaTeX as first-class scientific source and GraphRAG retrieval rules
5. [docs/HiveArchitectureBlueprint.md](HiveArchitectureBlueprint.md)
   - current Hive trust boundary, packet flow, queue, replay, and worker model
6. [docs/hive_greenfield_architecture.md](hive_greenfield_architecture.md)
   - packet/morphism/lambda-calculus reading of the Hive
7. [FORMALIZATION_PROTOCOL.md](../FORMALIZATION_PROTOCOL.md)
   - theorem-packet discipline, Pauli audit, and Lean closure rules
8. [hive-latex-blueprint.md](../hive-latex-blueprint.md)
   - LaTeX packet layer and LaTeX-to-Lean/Markdown linking intent
9. [.hermes.md](../.hermes.md), [GEMINI.md](../GEMINI.md), and
   [nemoclaw_config.yaml](../nemoclaw_config.yaml)
   - active agent routing, sidecar constraints, and runtime policy
10. Home-level runtime configs, when local policy inspection is needed:
   `/home/goutev/.codex/config.toml`, `/home/goutev/.codex/rules/default.rules`,
   `/home/goutev/.gemini/settings.json`,
   `/home/goutev/.gemini/trustedFolders.json`,
   `/home/goutev/.gemini/projects.json`,
   `/home/goutev/.gemini/antigravity/mcp_config.json`, and
   `/home/goutev/.hermes/config.yaml`
   - actual local trust, sandbox, model, MCP, and gateway envelopes
11. GitHub Copilot local surfaces, when Copilot routing matters:
   `/home/goutev/.copilot`, `/home/goutev/.cache/copilot`,
   `/home/goutev/.hermes/config.yaml`,
   `/home/goutev/.hermes/hermes-agent/agent/copilot_acp_client.py`,
   `/home/goutev/.hermes/hermes-agent/hermes_cli/copilot_auth.py`, and
   `tests/test_run_copilot_codex_lean_pipeline.py`
   - Copilot-backed model gateway, ACP client, and Lean proof-pipeline tests.
     Do not quote or copy private auth material from `/home/goutev/.hermes/auth.json`.

Use Black Books and long-form symbolic notes as source material, not closure
authority.  When using them, normalize into typed packets before editing code.

## Configured Agent Stack

The repo’s current operational vocabulary spans these configured roles.

| Surface | Role | Source |
|---|---|---|
| NemoClaw | local runtime/orchestration envelope | `nemoclaw_config.yaml` |
| OpenShell | sandbox/gateway envelope | `nemoclaw_config.yaml`, `docs/CANONICAL_AGENT_STACK.md` |
| Hermes | swarm manager / planner, not truth authority | `.hermes.md`, `/home/goutev/.hermes/config.yaml`, `tools/infra/hermes_config.yaml` |
| Codex CLI | OpenAI-backed execution lane; trusted local project with repo-specific sandbox policy | `/home/goutev/.codex/config.toml`, `/home/goutev/.codex/rules/default.rules` |
| GitHub Copilot | configured model gateway and ACP-capable assistant surface; Hermes currently targets `https://api.githubcopilot.com` | `/home/goutev/.hermes/config.yaml`, `/home/goutev/.copilot`, `/home/goutev/.cache/copilot`, `/home/goutev/.hermes/hermes-agent/agent/copilot_acp_client.py` |
| ClawCode / OpenClaw | gated execution alias/workspace surface used alongside Codex | `nemoclaw_config.yaml`, `/home/goutev/.gemini/projects.json` |
| Gemini CLI | explicit-operator creative sidecar only; never auto-routed | `.hermes.md`, `GEMINI.md`, `/home/goutev/.gemini/settings.json`, `/home/goutev/.gemini/trustedFolders.json`, `tools/infra/run_gemini_guarded.sh` |
| Gemini Antigravity | Gemini MCP/IDE-side memory and project integration surface | `/home/goutev/.gemini/antigravity/mcp_config.json` |
| Qwen planner | local high-level planning route | `nemoclaw_config.yaml`, `tools/infra/hermes_config.yaml` |
| DeepSeek prover | local Socratic/proof-search lane | `nemoclaw_config.yaml`, `tools/infra/hermes_config.yaml` |
| Goedel prover/auditor | conservative local audit lane | `nemoclaw_config.yaml`, `tools/infra/hermes_config.yaml` |
| Lean kernel / Lake | proof and build authority | `README.md`, `LOCAL_TOOLCHAIN_ARCHITECTURE.md` |
| Arango DAG 8529 | theorem/proof graph retrieval lane | `LOCAL_TOOLCHAIN_ARCHITECTURE.md` |
| Alexandria Arango 8530 | semantic/literature/Hive memory lane | `docs/alexandria/README.md`, `docs/hive_greenfield_architecture.md` |
| MotherBee / Hive workers | queue, packet motion, replay, deadend capture | `HiveArchitectureBlueprint.md`, `hive_greenfield_architecture.md` |

Gemini outputs are proposal-only until Codex reproduces and validates them.
Canonical edits require the Codex/ClawCode execution lane.  Hermes controls
motion through the system but cannot certify truth.

## Authority Split

Every representation can be useful memory.  Only validated representations can
increase authority.

| Lane | Validates | Authority |
|---|---|---|
| Lean 4 | `lake`, `lake env lean`, kernel, `InfoGeometry.Audit` | proof closure |
| LaTeX | parser/compiler/source-span checks | mathematical source structure |
| Python/SymPy | `py_compile`, tests, symbolic checks | executable sanity witness |
| Alexandria/Arango | schema, provenance, coverage, graph traversal | retrieval/navigation |
| LLM/Codex/Qwen/Gemini | repair, translation, synthesis, critique | proposal only |

The LLM/coding agent is a morphism worker.  It may generate, translate, repair,
and align representations.  It does not certify closure.

## Representation Labels

All packets, chunks, and edges that cross representation lanes should preserve
explicit labels.

```json
{
  "representation": "lean4 | latex | sympy | python | markdown | graph | vector",
  "role": "source | candidate | repair | verified | failed | explanatory",
  "authority": "kernel | compiler | parser | test | llm_inferred | human",
  "status": "raw | parsed | compiled | failed | proved | tested",
  "provenance": "deterministic | llm_generated | llm_repaired | human_seeded"
}
```

Alexandria source-format labels currently include:

- `text`
- `latex`
- `lean_ast`
- `python_ast`

Chunking strategy labels should include:

- `markdown_blocks`
- `latex_environment`
- `lean_ast_command`
- `python_ast_node`
- `cast_split_merge`

`cast_split_merge` is a structural normalization pass, not blind token
windowing.  It runs after deterministic chunking, splits large packets only at
paragraph/line boundaries, merges small adjacent compatible packets, and marks
indivisible oversize packets in provenance.

## Repair Loop

The compiler/formalizer loop is the same across Lean, LaTeX, and Python/SymPy:

```text
structured source
  -> parser/compiler/checker
  -> error or gap packet
  -> LLM repair proposal
  -> rerun parser/compiler/checker
  -> record accepted result or failed residue
```

For trilingual work:

```text
LaTeX intent
  -> candidate SymPy/Python witness
  -> candidate Lean theorem surface
  -> checks in all available lanes
  -> repair until one lane fails permanently or Lean closes
```

Failed attempts are first-class memory.  Store the source, candidate, error,
repair attempt, and gate result.  Do not overwrite deadends with summaries.

Alexandria repair lineage artifacts are:

- `alexandria_repair_attempts`
- `alexandria_repair_gate_results`
- `alexandria_repair_lineage_edges`

A clean repair may create a purified successor node with `active=true` and
`replacesNodeKey=<broken>`.  The lineage edge may carry
`activeReplacement=true`.  The broken node remains audit memory.

Cleanup is conservative: a broken node is better than a hole when it preserves
packet context, citation/source span, or graph connectivity.  Cleanup may
demote a duplicate or broken node from active retrieval, but it must preserve
or redirect every deterministic edge that depended on it before compacting
payloads.

## Deterministic vs LLM-Inferred Edges

Graph edges must distinguish parser/compiler structure from model inference.

```json
{
  "edgeType": "latex_label_ref",
  "provenance": "deterministic_latex_ref",
  "deterministic": true
}
```

```json
{
  "edgeType": "suggests_alignment",
  "provenance": "qwen_inferred",
  "deterministic": false,
  "confidence": 0.73
}
```

Do not let an inferred edge discharge a Lean proof obligation.  It can only
route retrieval, propose a bridge, or create a repair task.

## Minimal Workflows

### Lean Formalizer

1. Locate owner file and direct consumers.
2. Compile the owner or edited file with `lake env lean`.
3. If using graph context, descend to raw Lean declarations before editing.
4. Add theorem/definition/context or explicit debt.
5. Rebuild affected module; run audit gates when representation-depth tags are involved.

### LaTeX Formalizer

1. Preserve raw `.tex` as source evidence.
2. Extract theorem/proof/equation/citation packets.
3. Compile or parse the segment where possible.
4. Create candidate Lean/SymPy surfaces only with source spans and assumptions.
5. Record LaTeX parse/compile failures as repair tasks.

### SymPy/Python Formalizer

1. Parse with Python AST and preserve source spans.
2. Use SymPy only as an executable witness, not a proof authority.
3. Run `py_compile` and targeted tests.
4. Translate to Lean only through explicit assumptions and owner surfaces.

### Alexandria/Hive Worker

1. Ingest deterministic sources first.
2. Apply `cast_split_merge` only after deterministic packet boundaries exist.
3. Write coverage: every file is `digested`, `empty`, or `skipped`.
4. Add model-generated relations only with `provenance=llm_inferred`.
5. Record broken-node repair attempts through repair lineage.
6. Queue repair or formalization tasks rather than promoting semantic matches.

## Non-Negotiables

- Lean source and kernel checks decide formal truth.
- External databases are retrieval carriers, not proof authorities.
- LaTeX and SymPy can strengthen candidate generation but cannot close Lean claims.
- Symbolic/Black Book language must be normalized into typed packets before use.
- Every repair loop must preserve failure residue.
- Cleanup must preserve connectivity; do not replace broken memory with graph holes.
