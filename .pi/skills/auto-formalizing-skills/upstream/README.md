# auto-formalizing-skills

Fully Autonomous, multi-agent theorem proving system in Lean 4. Given an informal goal, it designs the proof top-down, writes every statement and decomposition proof into your Lean files, and dispatches agents to fill the leaves — until the headline theorem's `#print axioms` is clean.

The design is prompt-level and portable: it runs on any agentic coding tool that provides custom subagents, skills, and a persistent goal.

## Commands

- **`/prove <goal>`** — prove a headline theorem fully, top-down, to a `sorry`-free `#print axioms`.
- **`/check <statement>`** — hunt for a counterexample to a statement, grounded by running Lean.
- **`/handoff`** — wind an in-progress `/prove` down across conversations with no context loss.

## Requirements

- A Lean 4 + Mathlib project driven by Lake.
- An agentic coding tool with custom subagents, named skills, and a persistent goal.
- Capable models for the agents (the frontmatter pins Opus / Fable variants; adjustable. For example, GPT-5.6, GLM 5.2, or other models with Opus level capabilities).

## Install

```sh
git clone https://github.com/qinz1yang/auto-formalizing-skills.git
cd auto-formalizing-skills
```

Open your favorite vibe coding program in the cloned directory and paste the installer prompt from [`INSTALL.md`](INSTALL.md). It researches your setup, shows a plan, and changes nothing until you approve; then it copies the 13 files into your agent's config (`~/.claude/{commands,agents,prove}/` for the reference layout).

**Other harnesses.** The commands, agents, and protocol are plain Markdown prompts; only [`prove/prove-HARNESS.md`](prove/prove-HARNESS.md) (background spawn/resume, compaction) is specific to the reference harness. Hand the repo to an LLM on your tool and ask it to translate the entry points and remap that one file; the method ports unchanged.

## Usage

Run `/prove` with a goal — an informal description or a path to a plan file. For example:

```
/prove ricci flow short time existence
```

The run is autonomous and long-lived. It pauses only to ask a mathematical question (a convention fork, a headline restatement), and stops when the headline's axioms are exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx` or other axioms. Those three are the standard axioms of Lean's classical foundation that all of Mathlib rests on: a headline whose `#print axioms` shows exactly them has a complete, kernel-checked proof — `sorry`-free, and adding no axioms of its own.

`/check <statement>` runs a standalone counterexample hunt when you are unsure a lemma is true; it returns `FALSE` (with a runnable counterexample), `CONDITIONAL` (true only with an added hypothesis), or `NO-COUNTEREXAMPLE-FOUND`.

## Why top-down

Bottom-up construction — prove the lemmas first, then assemble them — requires knowing every details of the ingredients in advance. For a large theorem, the details are not completely known in advance. Even a strong model(like Claude Fable 5)'s up-front high-level plan may be wrong in ways that surface only later, by which point the flawed pieces are load-bearing. Building bottom-up, three failure modes recur:

- a whole pillar is missing at the top — for example, the Moser tame estimate;
- work that took days is unusable — an assumption that does not hold, a helper lemma stated too strongly to apply;
- the work was not needed at all.

Top-down descent avoids these. Each node is stated as exactly what its parent consumes. Only what a parent consumes is built, in the shape it is consumed — a helper cannot be too strong or too weak, because its statement is fixed by its consumer. A missing piece becomes an explicit `sorry` child when it is first required, and is built then; unreachable work is never dispatched. A mis-stated node is caught at the node, before anything is built on top of it. By immediately writing the proof after a node is posited, mistakes can be caught early and corrected before they propagate, together with refuter.

## Architecture

A `/prove` run is three tiers, each with a deliberately different scope and lifespan:

- **Leader** — the `/prove` conversation itself. Holds the mathematical direction in a small, protected context and gatekeeps every route. It does no proving and holds no engineering detail; it spawns and supervises one orchestrator.
- **Orchestrator** — one long-lived background agent. Drives waves of workers, ground-truths every return, owns the on-disk tactical state (`PLAN.md`), and absorbs all the engineering detail.
- **Workers** — short-lived, single-task agents: a *prover*, an *adversary* (refuter), and a *scout* (researcher). Spawned in parallel, each returns one result and ends.

A child cannot message its spawner, so the up-channel is the return value: a hard node is spawned in the background, returns its finding (which preserves its context), is ground-truthed, and is resumed by id with the orchestrator's ruling.

### Why a separate leader

The leader neither proves nor holds engineering detail — which is the point. Splitting it off the orchestrator buys three things:

- **Direction.** One tier holds only the mathematical path — what is proven, posited, or dead; the current crux; the mechanism a route relies on — and decides where the proof goes next. Strategy is not interleaved with tactics.
- **An independent check on the orchestrator.** The orchestrator drifts: it re-attempts a dead route, builds an orphan tower, or mis-judges a path after its own context degrades. The leader sees only its route reports and checks them against a separate model, catching errors the orchestrator cannot see from inside.
- **Context protection.** Engineering detail — Lean output, proof bodies, search logs, hundreds of dispatches — is what fills a context window and forces compaction, and it all lands on the orchestrator. The leader stays small, so it compacts rarely or never, and its direction does not degrade. A leader that absorbed the detail would compact repeatedly, and a compacted leader makes bad direction decisions.

## How it works

- **Assume-and-recurse.** Descend from the headline: design the tree, materialize each signature into its final file, glue each internal node from its children, fill the leaves. A worker that hits a missing prerequisite does not stop — it *posits* it (one `sorry` child with a precise signature), proves the target on top, and reports the child as the next recursion point.
- **Reading is not proving.** *Does it assemble?* is certified mechanically — compile the glue. *Is each leaf true as stated?* cannot be certified by reading, however adversarial; only a proof attempt certifies it. Audit budget goes to the headline (once, early) and a one-shot signature lint; the fill attempt is the backstop.
- **A dedicated adversary.** Almost every prover dispatch is paired with a concurrent *refuter* whose null hypothesis is that the statement is false. It attacks by reading against the trap catalog and by running a counterexample in a Lean scratch. If it refutes first, the racing prover is stopped and the statement restated — a cheap refutation spent to avoid an expensive proof of a false statement.
- **Ground truth over reports.** Every agent report is a suggestion from a partial view, never a conclusion. The orchestrator verifies each return against the compiler and disk — `#print axioms`, `lake build`, a `git diff` phantom-write guard, the elaborated declaration. Disk and the compiler are authoritative; the conversation is treated as a cache, and each tier re-hydrates from disk.
- **The trap catalog.** Fifteen recurring ways a plausible-looking statement is actually false, vacuous, over-strong, or mis-stated ([`prove/prove-TRAPS.md`](prove/prove-TRAPS.md)), distilled from real runs and screened at every signature's birth.
- **Honest completion.** One objective end condition: `#print axioms <headline>` is exactly `[propext, Classical.choice, Quot.sound]`. No deferred baseline, no partial credit. *Hypothesis-packaging* — adding a hypothesis whose type is the conclusion and returning it as the proof — is the severest violation, and is checked for at every tier.

## Layout

```
commands/   /prove, /check, /handoff
agents/     lean-worker, lean-worker-fable (provers), lean-refuter (adversary),
            lean-researcher (scout), prove-orchestrator
prove/      prove-PROTOCOL    the orchestrator's operating manual
            prove-CONTRACTS   the worker prompt-contracts
            prove-HARNESS     harness mechanics (tiers, compaction, resume)
            prove-RATIONALE   the case law — why each rule exists
            prove-TRAPS       the false-as-stated trap catalog
INSTALL.md         the installer prompt
CLAUDE.example.md  example project-conventions CLAUDE.md to adapt for your project
```

## Configuration

- **Models** — each subagent pins a `model:` in frontmatter; adjust to what your plan has.
- **Project conventions** — works best against a project whose `CLAUDE.md` documents its conventions; [`CLAUDE.example.md`](CLAUDE.example.md) is a starting template to adapt. Degrades gracefully without.

## License

[Apache 2.0](LICENSE).
