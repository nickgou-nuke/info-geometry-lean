---
name: chatgpt-history-to-hermes
description: Import ChatGPT export JSON into Hermes-compatible archives and durable memory candidates, with optional agentic-stack wiring via .agent/memory.
version: 1.0.0
author: Hermes Agent
license: MIT
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Treat witness packets, certificate fields, external certificates, assumption interfaces, literature owners, graph edges, and physics analogies as closure debt until discharged by kernel-checked Lean or imported mathlib theorems. Follow docs/CONSTRUCTIVE_CLOSURE_MANDATE.md; never promote anonymous or unformalized sockets as complete.

# ChatGPT History -> Hermes (Reusable Migration Pipeline)

Use this skill when the user wants to migrate ChatGPT chat history into Hermes and/or a shared `.agent/` memory layer (agentic-stack style).

## What this skill does

1) Normalizes ChatGPT export (`conversations.json`) into deterministic JSONL.
2) Produces human-readable session markdown archives (per conversation).
3) Extracts durable memory candidates (preferences, profile facts, recurring constraints).
4) Wires outputs into agentic-stack (`.agent/memory/...`) when present.
5) Supports Hermes memory ingestion from extracted candidates.

## Important limitation (current Hermes CLI)

There is no official one-command CLI to bulk-import arbitrary third-party transcripts directly into native Hermes session DB format.

So this skill uses a safe repeatable strategy:
- Session archive import surface: markdown + normalized JSONL under `~/.hermes/imports/chatgpt/`
- Durable memory import surface: `memory_candidates.jsonl` -> ingest to Hermes memory tool
- Optional shared stack surface: copy outputs into `.agent/memory/episodic/` and `.agent/memory/semantic/`

This avoids brittle direct SQLite writes.

## Inputs

- ChatGPT export zip (or extracted folder) containing `conversations.json`
- Optional target repository using agentic-stack with `.agent/` directory

## Outputs

Default output root:
- `~/.hermes/imports/chatgpt/`

Produced files:
- `normalized_conversations.jsonl`
- `sessions_md/<conversation_id>.md`
- `memory_candidates.jsonl`
- `migration_report.json`

## Process

### Step 1: locate export and run normalizer

Run script from this skill:

- `python3 <SKILL_DIR>/scripts/chatgpt_history_migrate.py --input /path/to/conversations.json --out ~/.hermes/imports/chatgpt`

If user has only zip:

- `mkdir -p ~/.hermes/imports/chatgpt/raw && unzip /path/to/chatgpt_export.zip -d ~/.hermes/imports/chatgpt/raw`
- then point `--input` to extracted `conversations.json`

### Step 2: verify artifacts

- confirm all four artifacts exist
- open `migration_report.json`
- sample-check 2-3 `sessions_md/*.md` files

### Step 3: ingest durable memory into Hermes

Load `memory_candidates.jsonl`, deduplicate by `(kind,key,value)`, and add only durable facts.

Rules:
- Import user preferences and stable profile facts first.
- Do NOT import one-off task logs or temporary project status.
- Keep entries compact and declarative.

### Step 4: wire to agentic-stack (optional)

If repo contains `.agent/`:

- `mkdir -p .agent/memory/episodic/chatgpt-import`
- `mkdir -p .agent/memory/semantic/chatgpt-import`
- copy session markdown to episodic:
  - `cp ~/.hermes/imports/chatgpt/sessions_md/*.md .agent/memory/episodic/chatgpt-import/`
- copy normalized + memory candidates to semantic intake:
  - `cp ~/.hermes/imports/chatgpt/normalized_conversations.jsonl .agent/memory/semantic/chatgpt-import/`
  - `cp ~/.hermes/imports/chatgpt/memory_candidates.jsonl .agent/memory/semantic/chatgpt-import/`

If `agentic-stack` CLI is installed, run a health pass:
- `agentic-stack status` (or `./install.sh status` in cloned stack repo)

## Quality gates

Before marking migration complete:

1) `migration_report.json` has non-zero conversations and messages.
2) At least 5 sample conversations render correctly in markdown.
3) Memory candidates reviewed; only durable items ingested.
4) If `.agent/` exists, copied files are present in episodic/semantic destinations.

## Pitfalls

- ChatGPT export schema variants exist; always normalize through script (never hand-parse ad hoc).
- Do not write directly into Hermes SQLite session DB.
- Avoid memory pollution: skip volatile details (temporary TODOs, timestamps of one-off runs, transient errors).

## Repeatable command block

Use this exact block for recurring migrations:

1) `python3 <SKILL_DIR>/scripts/chatgpt_history_migrate.py --input <conversations.json> --out ~/.hermes/imports/chatgpt`
2) Review `~/.hermes/imports/chatgpt/migration_report.json`
3) Ingest curated rows from `memory_candidates.jsonl` into Hermes memory
4) Optional `.agent/` wiring copy (episodic + semantic)

## Done criteria

- Normalized artifacts generated
- Memory candidates curated and ingested
- Optional agentic-stack wiring completed
- Final report delivered with counts + destination paths

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
- **Do not “resolve” debt with wording.** Progress must be structural, not just textual.
- **Do not remove debt labels** unless there is a native explicit Lean proof term checked by the kernel closing that specific debt.
- **Real progress** = replacing certificate/witness fields with theorem-backed native derivations.
