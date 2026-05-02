# Generative Loop Spec

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Not part of the maintained authority surface unless explicitly promoted.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

## Recurrent Scorpio->Virgo Pipeline for Autotheory Work

This defines a batch workflow that keeps generation high and closure honest.
It is explicitly symbol-first. Natural language is coordination-only.

## Loop Unit

One loop unit consumes one topic packet and outputs one admission decision.

### Step 1: Jungian pass (symbol generate)

- Input: topic packet + recent failures + current owner map.
- Prompt: `tools/prompts/jungian_pass.md`
- Output: symbolic motif packet + proof skeleton packet + unresolved contradictions.
- Must satisfy: `tools/prompts/SYMBOL_FIRST_PROTOCOL.md`.

### Step 2: Socratic regeneration (repeatable)

- Rephrase, reorder, compress, and amplify symbol relations and lemma chains.
- Use natural language only as short gloss for coordination.
- Run multiple passes until at least one coherent symbolic chain survives contradiction checks.
- Keep unresolved but high-value motifs alive.

### Step 3: Translator normalization (pre-formal)

- Convert each surviving symbolic claim into:
  - one pre-formal statement shape,
  - one likely owner path,
  - one likely bridge path.
- Remove claims that cannot name formal lane and first-goal shape.

### Step 4: Pauli pass (exclude/admit)

- Prompt: `tools/prompts/pauli_pass.md`
- Partition into:
  - `compiled`,
  - `bridge-drafted`,
  - `obstructed`,
  - `decorative`.

### Step 4: Batch patching

- Work in batches, not single-file churn.
- Apply minimal coherent patch set per batch:
  - one owner file,
  - one bridge/coherence file,
  - one doc/progress file.
Only apply this step for claims marked formalizable-now.

### Step 5: Verification

- run targeted build for changed module(s),
- then umbrella check when batch stabilizes.
- record first failing goal/error signature for unresolved claims.

### Step 6: Archive memory

- Record:
  - surviving motifs,
  - rejected motifs and why,
  - obstruction class.
  - symbolic deltas from compiler feedback.

---

## Stop Conditions

Stop the current loop when any condition holds:

1. two consecutive loops produce only decorative outputs,
2. no synthesis claim survives contradiction checks,
3. same blocker repeats twice with no narrowed assumptions.

On stop, move to:

- blocker minimization,
- theorem-neighborhood scan,
- or chapter-level reframing.

---

## Batch Cadence

Recommended cadence for one session:

1. run Jungian pass on 3 topics,
2. run Socratic regeneration passes on all three,
3. run one Pauli pass over the regenerated outputs,
4. pick top 2 formalizable-now candidates,
5. implement as one patch batch,
6. verify once.

This avoids expensive rebuild churn and prevents one-file tunnel vision.
