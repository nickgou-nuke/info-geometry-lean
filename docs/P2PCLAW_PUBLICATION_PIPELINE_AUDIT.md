# P2PCLAW Publication Pipeline Audit

> Status: `external reference`
> Audited: 2026-06-06
> Scope: OpenCLAW-P2P / P2PCLAW publication-preparation workflow.
> Authority: Lean source, `lake env lean`, and local repository policy remain
> proof authority. P2PCLAW is external publication and collaboration
> infrastructure only.

## Summary

`Agnuxo1/OpenCLAW-P2P` is best read as a publication-preparation and
decentralized research-front-door project, not as a theorem-proving dependency.
It documents a P2PCLAW ecosystem with a frontend, protocol material, agent
instructions, and links to an MCP/REST gateway for publishing and reviewing
research packets.

For this repository, its value is architectural:

- it models a paper/publication packet workflow;
- it separates frontend presentation from an MCP/REST service;
- it documents agent-facing usage through `llms.txt`;
- it suggests a tribunal/review loop that resembles our local
  aiClaw/GEPA/Lean-verifier furnace.

It must not become proof authority. External peer review, P2P network state,
agent prompts, and publication endpoints can at most produce review evidence or
publication artifacts. A mathematical claim is accepted here only after Lean
accepts the relevant owner file.

## External Surfaces Checked

Primary repository:

```text
https://github.com/Agnuxo1/OpenCLAW-P2P
```

Useful raw entry points:

```text
README.md
package.json
PROTOCOL.md
llms.txt
SECURITY.md
```

Important observation: the repository README displays an MIT badge, but GitHub
metadata reported no detected license and the raw `LICENSE` path was missing at
audit time. Do not copy code into this repository until the license is
clarified.

## What It Appears To Be

The audited frontend repository appears to be a public entry point for a
decentralized autonomous research collective:

- a Next/React/TypeScript application;
- documentation for research publication and peer review;
- protocol rules for agent participation;
- a pointer to the actual MCP/REST gateway repository;
- public endpoint documentation in `llms.txt`.

The likely technical integration target is not the frontend repo itself. The
more relevant target is the linked MCP/REST gateway:

```text
https://github.com/Agnuxo1/p2pclaw-mcp-server
```

That gateway should be inspected read-only before any integration work.

## Safe Interpretation For This Repository

Use P2PCLAW as a publication and review lane:

```text
Lean owner theorem
  -> focused build
  -> theorem/debt manifest
  -> paper packet
  -> local oracle review
  -> optional external publication gateway
```

Do not use it as a proof lane:

```text
external reviewer response
  != Lean proof

external publication status
  != theorem verification

external protocol compliance
  != repository policy
```

## Security Boundary

The external protocol asks agents to connect to public coordination endpoints.
That is not safe as an automatic repository behavior.

Forbidden by default:

- auto-connecting cron or browser agents to public hive endpoints;
- importing external system prompts into the proof oracle;
- letting an external service mutate source files;
- sending secrets, cookies, private keys, browser session data, or full
  unfiltered repo dumps;
- accepting external publication or peer-review status as proof closure;
- consuming unlicensed source code.

Allowed with explicit user direction and local dry-run gates:

- read-only inspection of public documentation;
- read-only API schema inspection;
- local packet generation that is not submitted externally;
- manually approved publication submission of an already Lean-verified paper
  packet;
- isolated adapter experiments under `tools/infra/`, with no source mutation
  unless a focused Lean build passes.

## Publication Packet Shape

A useful local packet for future publication should contain:

```json
{
  "title": "short paper title",
  "abstract": "human-readable summary",
  "owner_modules": [],
  "main_theorems": [],
  "definitions": [],
  "build_commands": [],
  "build_status": "focused-build-closed",
  "lean_version": "v4.28.0",
  "mathlib_revision": null,
  "repo_commit": null,
  "open_closure_debt": [],
  "oracle_reviews": [],
  "source_links": [],
  "license_notes": [],
  "submission_target": "local-only|p2pclaw|arxiv|journal"
}
```

The packet should be generated from repo-local evidence:

- Lean files and declaration names;
- `lake env lean` or `lake build` output;
- explicit `sorry`/debt audit results;
- source citations;
- local oracle review transcripts;
- provenance hashes for generated artifacts.

## Mapping To Existing Local Infrastructure

Relevant local pieces already exist:

- `docs/AICLAW_CHATGPT_REVIEW_RUNBOOK.md`
- `docs/PROOF_SEARCH_ORCHESTRATOR_CONTRACT.md`
- `docs/DEBATE_ORACLE_CONVERGENCE_MAP.md`
- `tools/infra/aiclaw_audit_runner.py`
- `tools/infra/proof_seeker.py`

The correct local architecture is:

```text
candidate theorem file
  -> aiClaw queue
  -> one complete prompt
  -> one complete replacement candidate
  -> compile in tmp candidate path
  -> promote only on Lean success
  -> record outcome for GEPA/regression
  -> produce paper packet
```

The external P2PCLAW lane can be added only after this local chain is stable.

## Institute-Scale Role

For a DGX Spark / local institute setup, P2PCLAW-like infrastructure belongs at
the publication boundary:

1. Local proof authority: Lean and Mathlib.
2. Local retrieval memory: DAG, Arango, LeanTrail, archive mirrors.
3. Local oracle debate: aiClaw, browser recovery, GEPA prompt regression.
4. Local paper generator: theorem/debt/source packet to Markdown or LaTeX.
5. External publication gateway: optional, audited, manually approved.

This gives the institute a clean split:

```text
inside boundary: proof construction, verification, provenance
outside boundary: publication, review, discovery, collaboration
```

## Open Decisions

- Inspect `Agnuxo1/p2pclaw-mcp-server` read-only.
- Decide whether to add an external reference checkout under `external_refs/`
  after license review.
- Define a local `publication_packet.json` schema.
- Add a dry-run-only exporter from Lean theorem metadata to paper packets.
- Decide whether external submission is ever allowed from automation, or only
  through a manual operator command.

## Current Recommendation

Do not clone or vendor OpenCLAW-P2P yet. Treat it as an external publication
architecture reference. Inspect the MCP server next, then implement a local
paper-packet generator that can later target P2PCLAW, arXiv, or an institute
archive without changing the proof pipeline.
