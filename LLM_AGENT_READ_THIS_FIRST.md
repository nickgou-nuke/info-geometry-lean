# LLM Agent — Read This First

**You are about to modify representation-theoretic, categorical, or
Grothendieck-related code.**

**STOP.** Read these files before making any changes:

1. **`AGENTS.md`** — Repository agent routing rules (2-minute read)
2. **`docs/CANONICAL_AGENT_PIPELINE.md`** — Current repo path, tool routing,
   aiClaw queue discipline, Pi extension stack, GEPA flow, and forbidden
   legacy routes (2-minute read)
3. **`docs/CATEGORICAL_INFRASTRUCTURE_MAP.md`** — Complete map of existing
   categorical/Grothendieck/colimit infrastructure (10-minute read)

## Why

The categorical layer (`Algebra/Grothendieck.lean`, `Categorical/`,
`Canonical/TensorTowerColimit.lean`, `Quantum/RealKCategory.lean`,
`Clifford/LogCftMonodromy.lean`) is the **owner layer**.

Matrix-level files (`Canonical/FiniteFibonacci*.lean`,
`Algebra/FibonacciParafermion.lean`) are **instances** of categorical
theorems, never replacements for them.

LLM coding agents repeatedly lose this context and write redundant
matrix-level code that already exists at the categorical level.
This file exists to prevent that.

## Quick checks before writing any new `def` or `theorem`:

| If you need... | Check first... |
|---------------|----------------|
| A Grothendieck group | `Algebra/Grothendieck.lean` (universal construction exists) |
| A colimit of modules | `Canonical/TensorTowerColimit.lean` |
| A colimit with invariants | `Canonical/ErlangenColimitResolution.lean` |
| Fibonacci fusion theorem | `Categorical/FibonacciBraiding.lean` |
| A real category with K² = -I | `Quantum/RealKCategory.lean` |
| Log CFT monodromy | `Clifford/LogCftMonodromy.lean` |
| A bridge file | Don't. Use `import` directly. |

## Proof Architecture Mandates (2026-06-06)

Before adding ANY field to a structure or ANY axiom to a definition:

| Check | Skill to load |
|-------|--------------|
| Is this field a genuine axiom (never proven before)? | `axiom-legitimacy-check` |
| Is this field structurally necessary (not a disguised theorem)? | `constructive-definition-discipline` |
| Is this structure a socket (short-circuiting a known construction)? | `socket-debt-honesty` |
| Do you know the exact mathlib4 lemma name? | `mathlib-api-discovery` |
| Are you formalizing a theorem from scratch? | `lean-vibe-formalization` |

### The Iron Rules

1. **Zero fake axioms.** If Tomita-Takesaki proved J exists from (M, φ), you cannot postulate J as a primitive without marking it as a socket.
2. **One propositional field max.** Structures carry carrier data + codomain constraints only. J²=1 is a theorem, not a field.
3. **Honest sorries.** Unproven theorems stay as `by sorry`. Never disguise debt as "axioms."
4. **Search before you guess.** `rg` + `loogle` beat hallucinated lemma names.
| Are you debugging a stubborn compile error? | `socratic-oracle-proof-repair` |

5. **Bidirectional equivalence.** An axiomatic characterization is legitimate IF there's a theorem: `(constructive) ⇔ (axiomatic)`. The debt is the equivalence proof, not the axioms.

## The Oracle Route (for Stubborn Errors)

If you have tried to fix a compile error 3+ times and failed:

1. **Stop single-shot patching.** You are making it worse.
2. Load the `socratic-oracle-proof-repair` skill.
3. Send the COMPLETE owner file + ALL relevant build errors to ChatGPT via
   aiClaw clawbot. Do not send whole-repo dumps or secrets.
   Prefer:
   `python3 tools/infra/socratic_clawbot.py --file <owner.lean> --theorem <name> --dry-run --json`
   before the real send.
4. **Wait 3-5 minutes** for deep thinking. Do not interrupt.
5. If aiClaw returns `Thinking`, do not send another prompt; read the final
   visible answer from the browser/DevTools route.
6. Apply the oracle's answer in ONE integrated patch. Build once.
7. If errors remain, send the NEW build output back to the same conversation.

This pattern closed a `zorn_subset` type mismatch that survived 30+ manual iterations. The oracle found the fix in 3 minutes.
