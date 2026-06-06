---
name: socratic-oracle-proof-repair
description: Use when a stubborn Lean 4 proof error should be repaired through a Socratic ChatGPT oracle via aiClaw. Send the complete owner file plus all relevant build errors in one prompt, wait for the final visible answer, request one complete corrected Lean file, and accept only Lean-kernel-checked code.
---

# Socratic Oracle Proof Repair

Use this skill when a Lean proof has survived repeated local attempts and needs
an external chatbot auditor/repair assistant through aiClaw.

## Core Rule

The oracle is a Socratic repair assistant, not proof authority.

- ChatGPT via aiClaw: diagnoses the proof failure and suggests a repair.
- Codex/coding agent: owns source edits and integration.
- Lean kernel: decides truth.
- SymPy/Arango/DAG: evidence and navigation only.

The successful pattern is not blind manual patching. It is:

```text
complete owner file + all relevant build errors
  -> one ChatGPT oracle prompt through aiClaw
  -> wait for the final visible answer
  -> request one complete corrected Lean file
  -> Codex performs the source edit
  -> run Lean
  -> if errors remain, send the new complete error output back
```

## Formal Precedent

The external reference for adversarial dialogue is:

```text
external_refs/deepmind-debate
```

Use it as a design precedent, not as imported proof authority. It formalizes a
stochastic oracle debate where honest Alice/Bob beat adversarial Eve under
finite probabilistic completeness/soundness guarantees. The key declarations
are `Correct`, `completeness`, `soundness`, and `correctness`.

Do not call this an asymptotic convergence theorem. The nearby analytic
convergence source is separate:

```text
external_refs/lean-stat-learning-theory/SLT/ConvergenceL1Subseq.lean
```

That file proves `L1` convergence gives an almost-everywhere convergent
subsequence; it has no adversarial dialogue protocol. See:

```text
docs/DEBATE_ORACLE_CONVERGENCE_MAP.md
```

## When To Trigger

Use this skill when:

- a Lean compile/type/rewrite error survived several local repair attempts
- a theorem uses subtle mathlib API semantics (`zorn_subset`, order maximality,
  dependent rewriting, category/coherence APIs, typeclass inference)
- the user explicitly asks to use aiClaw, ChatGPT, oracle, Socratic proof
  repair, or the Jung-Pauli proof lane

Do not use it to:

- replace local Lean diagnostics and repo search
- send secrets or whole-repo dumps
- accept chatbot prose as proof
- claim hidden chain-of-thought recovery

## Preflight

1. Identify the owner file and exact theorem.
2. Run the narrow Lean check and capture all relevant build output.
3. Read the complete owner file, not just the failing line.
4. Remove secrets and unrelated private data from the prompt.
5. Hash or record prompt length for the event trace.

Prefer:

```bash
lake env lean <owner-file>
```

If a full module build is required, record the exact command.

## Oracle Prompt

For stubborn proof failures, do not under-contextualize. Send the complete
owner file plus complete relevant build errors for that file.

Prompt shape:

````text
Review this Lean 4 proof failure as a concrete repair task.
Repo: info-geometry-lean.
Owner file: <path>.
Target theorem: <name>.

The complete owner file is below.
<file>

The complete relevant Lean build output is below.
<errors>

Return:
1. the actual cause,
2. the complete corrected Lean owner file,
3. any mathlib API semantic correction.

Canonical response format:

### Cause
One concise paragraph.

### Replacement
```lean4
-- Full corrected Lean file content only.
-- No diff hunks, no theorem fragments, no prose inside the code block,
-- no one-line minification.
```

### API
One concise paragraph, or "No API correction."

Do not propose broad rewrites. Keep the file small and mathlib-style:
minimal imports, cohesive owner scope, short local helper lemmas, no
architecture expansion. Do not hide the proof in wrappers, certificates,
axioms, or vacuous theorems.
````

## aiClaw Discipline

Use the repo wrapper where possible:

```bash
python3 tools/infra/aiclaw_chat.py queue-status --platform chatgpt
python3 tools/infra/aiclaw_chat.py wait --wait-timeout 30 --interval 1 --quiet
python3 tools/infra/aiclaw_chat.py ask --dry-run --prompt "$PROMPT"
python3 tools/infra/aiclaw_chat.py ask --wait --new --json --prompt "$PROMPT"
```

For Lean owner-file proof repair, prefer the fused wrapper, which builds the
complete owner-file plus Lean-output prompt and delegates the send to
`aiclaw_chat.py`:

```bash
python3 tools/infra/socratic_clawbot.py \
  --file <owner-file.lean> \
  --theorem <theorem_name> \
  --dry-run --json
python3 tools/infra/socratic_clawbot.py \
  --file <owner-file.lean> \
  --theorem <theorem_name> \
  --response-out artifacts/oracle/<theorem>.md \
  --json-out artifacts/oracle/<theorem>.json
```

Operational rules:

- Send one prompt.
- Treat each chatbot platform as a single-flight queue: query in, final answer
  out, then the next query may enter.
- Wait 3-5 minutes for deep responses on hard proof failures.
- Do not stack another prompt over an unresolved answer.
- If aiClaw returns `content: "Thinking"`, do not resend.
- Recover the final visible answer read-only from DevTools/browser DOM.
- Release a held lane only after visible final-answer readback:
  `python3 tools/infra/aiclaw_chat.py queue-release --platform chatgpt --reason final_visible_answer_recorded`.
- Continue the same conversation only when sending new build errors after a
  checked replacement still fails.

Detailed aiClaw readback procedure:

- `docs/AICLAW_CHATGPT_REVIEW_RUNBOOK.md`

## Apply The Answer

Use the oracle answer as a full-file replacement candidate, then build. Do not
ask for or apply fragmented diffs or theorem-only snippets from the chatbot.

Rules:

- replace the broken owner file with the complete corrected owner-file content
- preserve user changes
- keep the file small and mathlib-style: minimal imports, cohesive purpose,
  and local helper lemmas only when they reduce the proof
- no `sorry`, `admit`, `axiom`, fake instance, wrapper, certificate, or `True`
  closure
- verify any claimed mathlib theorem with `#check` or local source search
- run the narrow Lean check after inserting the replacement

For order/Zorn repairs, inspect the actual return shape. Example lesson:

```text
obtain m and hmMax from zorn_subset S hchain
split hmMax into hmS and hmMax'
```

Do not assume `zorn_subset` returns a triple `exists m in S, ...`; check the actual
maximality structure and prove equality from both subset directions, e.g.
`Set.Subset.antisymm`.

## Event Trace

Record:

```text
socratic oracle proof repair:
- owner file:
- theorem:
- local command:
- prompt chars/hash:
- sent once:
- aiClaw platform status:
- answer read method: aiClaw final / DevTools DOM readback
- useful oracle claim:
- replacement summary:
- verification command:
- verification result:
```

Do not record or claim private chain-of-thought. Only visible messages,
diagnostics, commands, and kernel-checked changes are auditable.

## Done Criteria

- target file checks with Lean
- no proof-debt shortcut was added
- chatbot contribution is recorded as review evidence
- no unresolved response was overwritten by a second prompt
- remaining warnings or lint suggestions are reported honestly
