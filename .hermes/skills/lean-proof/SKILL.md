---
name: lean-proof
description: Use when asked to prove something in Lean. Covers one-step-at-a-time proving, error priority, working on the hardest case first, proof cleanup, skill discovery and loading, evolution pipeline skill registration, handling unknown skill failures, handling dependent type rewriting issues, and verification gates.
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Treat witness packets, certificate fields, external certificates, assumption interfaces, literature owners, graph edges, and physics analogies as closure debt until discharged by kernel-checked Lean or imported mathlib theorems. Follow docs/CONSTRUCTIVE_CLOSURE_MANDATE.md; never promote anonymous or unformalized sockets as complete.

## Evolution Pipeline: Registering Generated Skill Variants

This skill participates in an evolution (self-evolver) pipeline. The pipeline mutates this SKILL.md, writes the result to `quarantine/hermes_skills/evolved/lean-proof/gen_NNN/SKILL.md`, and then tests the variant by loading it.

**The test step fails** when a variant is loaded by filesystem path instead of by registered name. To correctly test a generated variant:

### Correct Loading: Register Then View

```python
# Step 1: Register the generated skill by name
skill_manage(
    action="create",
    name="lean-proof-gen-NNN",  # or any unique name
    content=read_file("quarantine/hermes_skills/evolved/lean-proof/gen_NNN/SKILL.md")
)

# Step 2: Load the registered skill by name
skill_view(name="lean-proof-gen-NNN")
```

### INCORRECT (causes failure)

```python
# WRONG: Filesystem paths are NOT skill names
skill_view(name="quarantine/hermes_skills/evolved/lean-proof/gen_000")
# Error: Unknown skill(s): quarantine/hermes_skills/evolved/lean-proof/gen_000
```

### Cleanup After Testing

After testing, remove the temporary skill registration:

```python
skill_manage(action="delete", name="lean-proof-gen-NNN", absorbed_into="")
```

### Evolution Pipeline Integration Checklist

When this skill is being evolved or tested by a self-evolver pipeline:

1. Read the mutated SKILL.md from `quarantine/hermes_skills/evolved/lean-proof/gen_NNN/SKILL.md`
2. Register it: `skill_manage(action="create", name="lean-proof-gen-NNN", content=...)`
3. Load it: `skill_view(name="lean-proof-gen-NNN")`
4. Execute the proof task using the loaded skill
5. Clean up: `skill_manage(action="delete", name="lean-proof-gen-NNN", absorbed_into="")`
6. Collect the outcome and fitness score

Never pass a filesystem path as a `name` parameter to `skill_view()`. Only registered skill names work.

## Before Starting: Skill Discovery and Loading

Always search for and load relevant skills before beginning proof work. This prevents "unknown skill" failures and ensures you have the right tooling.

### Skill Discovery

Use `skills_list()` to discover available skills, then `skill_view(name)` to load full content:

```
skills_list()                              # see all skills
skills_list(category="lean4-skills")       # Lean-specific skills
skills_list(category="software-development") # repo workflow skills
```

### Loading Skills

Load relevant skills by **registered skill name only** — never by filesystem path:

```
skill_view(name="lean4")                      # Lean 4 tooling, LSP commands, mathlib search
skill_view(name="native-proof-closure-mandate")  # Hard closure-debt reduction policy
skill_view(name="proof-root-hole-repair")     # Lean proof repair for semantic holes
```

### NEVER Reference Skills by Filesystem Path

**Do not** reference skills by filesystem path like:
```
skill_view(name="/home/goutev/repos/info-geometry-lean/quarantine/hermes_skills/evolved/lean-proof/gen_000")
# ^^^ WRONG — this will fail with "Unknown skill(s)"
```

Always use the registered skill name (the `name:` field in the skill's YAML frontmatter). If you don't know the name, use `skills_list()` to find it.

### Error Recovery: Unknown Skill

If `skill_view(name=...)` returns an "Unknown skill(s)" error:

1. Check the name you passed — is it a filesystem path instead of a registered name?
2. Run `skills_list()` to find the correct name
3. If the skill genuinely doesn't exist, proceed without it rather than fabricating a path
4. Log the missing skill as a discovery gap — do not silently retry with a guessed path or filesystem path

## Which Lean Skill to Load

| Situation | Load this skill first |
|-----------|----------------------|
| Editing .lean files, debugging builds, mathlib search | `lean4` |
| Replacing hypothesis/witness/certificate scaffolding with native proofs | `native-proof-closure-mandate` |
| Repairing proof holes, fake bridges, or wrapper projections | `proof-root-hole-repair` |
| Writing a new theorem corridor from scratch | `lean4` + this skill |
| Triage of strict-check CI blockers | `strict-check-artifact-triage` |
| Reducing closure debt in a specific corridor | `graph-guided-closure-debt` |

# Lean Proof Methodology

These are non-negotiable constraints for writing Lean proofs correctly.

## One Step at a Time

Write one tactic, check diagnostics (use `done` to see unsolved goals), repeat. Never write multiple tactics before checking.

**`by sorry` is acceptable**: For placeholders you're not actively working on.
**`done` is required**: When you expect there to be next steps in an active proof.

## Error Priority

Fix errors in this order — higher-priority errors make lower-priority ones unreliable:

1. **Syntax errors** -> 2. **Type errors** -> 3. **Unsolved goals / tactic failures** -> 4. **Linter warnings**

"Unsolved goals" errors appear on `by` or `=>` lines, NOT where you add tactics. If there's an "unsolved goals" on line 59 but a tactic error on line 65 -- fix line 65 FIRST.

Stop writing tactics after any error.

## Work on the Hardest Case First

### Across Theorems

Go directly to the target theorem. Don't fill in `sorry`s in helper lemmas first -- Lean treats `sorry` as an axiom, so dependent theorems still work.

Move sorries earlier in the file by replacing a `sorry` proof with references to simpler lemmas:

```lean
-- Before:
theorem main_theorem : A = C := by sorry

-- After:
theorem lemma1 : A = B := by sorry
theorem lemma2 : B = C := by sorry
theorem main_theorem : A = C := by
  rw [lemma1, lemma2]
```

### Within a Proof

When a proof has multiple cases, `sorry` the easy cases and work on the hardest one first. If the hard case fails, effort on easy cases is wasted.

```lean
match n with
| 0 => sorry -- fill in later
| 1 => sorry -- fill in later
| n + 2 => -- WORK ON THIS FIRST
```

## Proof Cleanup

After getting a proof to work, clean it up immediately:
- Combine redundant steps (`rw [a]; rw [b]` -> `rw [a, b]`)
- Test if `simp` can handle more (remove earlier steps one by one)
- Find the truly minimal proof

## Comment And Docstring Discipline

In `info-geometry-lean`, explanatory comments may be part of the theorem
transport substrate. They often map between SymPy, Python, Lean 4, LaTeX,
natural language, and physics-of-information terminology.

Do not shorten comments by default while proving. Preserve bridge-bearing prose,
expand it when needed for semantic accuracy, and correct it when it misstates
the formal object. Delete prose only when it is stale, false, duplicative, or
not carrying a representation bridge.

## Dependent Type Rewriting Issues

**When you encounter "motive is not type correct" or similar errors during rewriting:**

### The Problem

Rewriting a term `b` that appears in dependent types (like `hab : a <= b`) fails because the motive cannot abstract over the dependencies.

```lean
have hb : b = f x
rw [hb]  -- Error: motive is not type correct
```

### The Solution: Generalize First, Instantiate Last

Prove a generalized statement for an arbitrary parameter, then instantiate:

```lean
suffices forall s, statement_about s by
  have h_specific := the_equality_you_have
  convert this ?_ <;> exact h_specific
intro s
-- Now prove the general statement for arbitrary s
```

This works because the generalized statement has no dependencies on the problematic term, and `convert` handles the dependent type coercions at the end.

### Alternative: `generalize` tactic

When the above pattern is awkward, use `generalize` to abstract the problematic term:

```lean
generalize hb : b = x
-- b is now replaced by x everywhere, with hb : b = x
-- Prove the goal for x, then subst hb
```

## Verification Gates

### File-Level Gate

After editing a `.lean` file, verify it compiles:

```bash
lake env lean path/to/File.lean
```

Run this from the project root. It catches syntax and type errors faster than a full build.

### Module-Level Gate

After a batch of edits, build the minimal module target:

```bash
~/.elan/bin/lake build Module.Name
```

Use the project's locked wrapper if available:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock Module.Name
```

### Project Gate

Before committing, run the full project build:

```bash
lake build
```

### Completion Criteria

A proof is complete only when ALL of these hold:

1. `lake build` passes (or the locked module build passes) with zero errors
2. Zero `sorry` placeholders remain in the agreed scope
3. Only standard axioms are used: `propext`, `Classical.choice`, `Quot.sound`
4. No theorem/lemma statements were changed without explicit permission
5. No witness/certificate/wrapper fields remain as substitutes for real proof
6. No debt markers (explicit `sorry`, `admit`, `axiom`) remain in the touched modules

**Never declare a proof complete while `sorry` placeholders, debt markers, or uncompiled code remain.** The build gate is necessary but not sufficient -- green builds can still carry explicit closure debt. Separate "build-green" from "native-closed" when reporting status.

## Automation Tactics Cascade

When stuck on a goal, try these in order (stop on first success):

`rfl` -> `simp` -> `ring` -> `linarith` -> `nlinarith` -> `omega` -> `exact?` -> `apply?` -> `grind` -> `aesop`

Note: `exact?`/`apply?` query mathlib (slow). `grind` and `aesop` are powerful but may timeout. For detailed tactic guidance, load the `lean4` skill and use its LSP tools (`lean_goal`, `lean_multi_attempt`, `lean_hammer_premise`).

## Stuck or Error Recovery

When a tactic or approach fails repeatedly:

1. **Step back** -- read the full goal state with `lean_goal(file, line)`
2. **Search mathlib** -- use `lean_local_search("keyword")` or `lean_leanfinder("goal query")` for relevant lemmas
3. **Change course** -- if rewriting fails, try `calc` blocks. If `simp` loops, try explicit `rw`. If a direct approach stalls, try an indirect lemma.
4. **Cut scope** -- replace the stuck proof with a clearly marked `sorry`, rebuild the rest of the file to verify it's structurally sound, then return to the blocker in isolation
5. **Escalate** -- load the `lean4` skill and use `/lean4:prove` or `/lean4:autoprove` for guided multi-cycle proving

Do not repeat the same failing command more than twice without changing the proof shape.
