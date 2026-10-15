# Installing auto-formalizing-skills

This package adds three slash commands — **`/prove`**, **`/check`**, **`/handoff`** — plus the five subagents and five protocol documents they depend on, for top-down formalization of mathematics in **Lean 4**.

Because the files reference each other by absolute path (`~/.claude/prove/...`, `~/.claude/agents/`), they install into your agent's user config directory (`~/.claude/`):

| From (this repo) | To |
| --- | --- |
| `commands/*.md` (3 files) | `~/.claude/commands/` |
| `agents/*.md` (5 files) | `~/.claude/agents/` |
| `prove/*.md` (5 files) | `~/.claude/prove/` |

**Prerequisites:** a coding agent with custom subagents, skills, and a persistent goal; a Lean 4 + Lake project to run it on; access to the models the subagents pin in their frontmatter (Opus / Fable — adjustable during install).

---

## One-shot install (recommended)

Clone this repo, open your coding agent **inside the cloned folder**, and paste the prompt below. It researches your environment first, shows you a plan, and **changes nothing until you approve it.**

```text
You are helping me install a skill package called "auto-formalizing-skills" — a
multi-agent system for formalizing mathematics in Lean 4 (the /prove, /check, and
/handoff commands plus their supporting subagents and protocol documents).

Work in FOUR phases. Do NOT create, copy, move, or modify ANY file until I have
explicitly approved your plan in Phase 2. Treat Phase 1 as strictly read-only.

## Phase 1 — Research (read-only, change nothing)

1. Locate the package. Find the directory containing all three subfolders `commands/`,
   `agents/`, and `prove/` — usually your current working directory. If you cannot find
   it, ask me for the path. Confirm all 13 expected files are present:
     - commands/: prove.md, check.md, handoff.md
     - agents/:   lean-worker.md, lean-worker-fable.md, lean-refuter.md,
                  lean-researcher.md, prove-orchestrator.md
     - prove/:    prove-PROTOCOL.md, prove-CONTRACTS.md, prove-HARNESS.md,
                  prove-RATIONALE.md, prove-TRAPS.md
   If any are missing, STOP and tell me — the download is incomplete.

2. Determine the install target. These files use hard-coded absolute paths
   (`~/.claude/prove/...`, `~/.claude/agents/`), so they must go into the agent's user
   config directory (`~/.claude/` on macOS/Linux; the equivalent elsewhere):
     - commands/*.md  ->  ~/.claude/commands/
     - agents/*.md    ->  ~/.claude/agents/
     - prove/*.md     ->  ~/.claude/prove/
   Report which of these three target directories already exist.

3. Check for collisions. For each of the 13 files, check whether a file of the SAME NAME
   already exists at its destination, and whether its contents differ. List every
   collision. Only these 13 named files are in scope — you must never delete, move, or
   overwrite any OTHER file in those directories.

4. Report, do not change:
   - The subagents pin specific models in their frontmatter (Opus / Fable variants).
     List each agent's pinned `model:` so I can confirm I have access to them.
   - Confirm there is a Lean 4 + Lake project in the working directory (a `lakefile.lean`
     / `lakefile.toml`). /prove operates on whatever project is in the working directory;
     no project name needs to be configured.

5. Summarize everything you found in a short report.

## Phase 2 — Plan, then get my explicit permission

Present a concise plan:
  - The exact list of the 13 files -> their destinations.
  - How you will handle each collision. Recommend: back up the existing file to
    `<name>.bak-<timestamp>` before overwriting it. Ask me to choose per-collision or
    globally between {overwrite-with-backup, skip}.
  - One optional step, performed ONLY if I say yes: if I lack access to a subagent's
    pinned model, help me pick an available model and update that agent's `model:`
    frontmatter in the installed copy.
Then STOP and wait for my explicit approval. Do not touch anything until I approve.

## Phase 3 — Install (only after I approve)

  - Create `~/.claude/commands`, `~/.claude/agents`, `~/.claude/prove` if missing.
  - Copy the 13 files to their destinations, handling collisions exactly as I approved.
  - Perform the optional step if I approved it.
  - Verify: list the installed files at their destinations and confirm each is non-empty.

## Phase 4 — Report

Tell me:
  - What was installed where, and what (if anything) was backed up.
  - That `/prove`, `/check`, `/handoff` and the subagents become available after I
    restart my coding agent.
  - A one-line description of each of the three commands so I know what I now have.
```

---

## Manual install (fallback)

If you'd rather not use the prompt, from the repo root:

```sh
mkdir -p ~/.claude/commands ~/.claude/agents ~/.claude/prove
cp commands/*.md ~/.claude/commands/
cp agents/*.md   ~/.claude/agents/
cp prove/*.md    ~/.claude/prove/
```

Restart your coding agent so the new commands and subagents are picked up.

> **Note on models.** The subagents pin specific models (`model:` in their frontmatter);
> adjust them if your plan differs.
