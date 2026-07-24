# Autonomous Self-Improving Proof Chain — Architecture

> Authority: this is a proposal-and-verification system, NOT an autonomous proof authority.
> Proof authority remains: Lean source, kernel-checked proof terms, `lake env lean`, narrow builds.
> Everything else (Arango, browser audit, ChatGPT, DeepSeek, arXiv, GEPA) is a proposal sidecar.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    ArangoDB / hive_live                     │
│  - hive_tasks queue  - proof-search  - skill-evolution     │
└────────────────────────────┬────────────────────────────────┘
                             │
              ┌──────────────┴──────────────┐
              ▼                              ▼
┌─────────────────────────┐    ┌──────────────────────────────┐
│ seed_goals_from_sorries │    │ evolution_worker.py (disabled)│
│ scans Lean sorry debt   │    │ polls evolution tasks        │
│ seeds exact queue tasks │    │ runs evolution pipeline      │
└─────────────────────────┘    └──────────────┬───────────────┘
                                              │
                                              ▼
                             ┌────────────────────────────────┐
                             │ gepa_evolver.py                │
                             │ DSPy GEPA skill evolution      │
                             │ mutation / reflection / select │
                             └──────────────┬─────────────────┘
                                            │
                     ┌──────────────────────┼──────────────────────┐
                     ▼                      ▼                      ▼
           ┌──────────────┐    ┌─────────────────┐    ┌──────────────────┐
           │skill_mutator │    │evaluator         │    │vacuity_critic    │
           │mutates skills│    │grounded scoring  │    │learns failure    │
           └──────────────┘    └─────────────────┘    └──────────────────┘
                                            │
                                            ▼
                             ┌────────────────────────────────┐
                             │ proof_seeker.py                │
                             │ searches: mathlib, Alexandria, │
                             │ arXiv, web                     │
                             └────────────────────────────────┘
                                            │
                                            ▼
                             ┌────────────────────────────────┐
                             │ Archive / lineage manifests    │
                             │ quarantine/hermes_skills/      │
                             └────────────────────────────────┘

Optional proposal sidecars:
  - ChatGPT browser harness (CDP)
  - Pi / DeepSeek coding-agent lanes
```

## Authority Model

**Authoritative:**
1. Lean declarations in current repo source
2. Kernel-checked proof terms
3. `lake env lean <file>`
4. Narrow locked builds where applicable

**Non-authoritative (useful proposals):**
- Arango queue state
- Browser audit output / ChatGPT output
- DeepSeek / Pi coding output
- arXiv / web / Alexandria retrieval
- GEPA fitness proposals / skill mutations

## Success Criteria

A run is only genuinely successful if:
- Target theorem stated honestly
- Proof is native Lean OR remaining debt is explicit
- Target file compiles with `lake env lean`
- No `_True` / `_holds` / `_certificate` fake closure introduced
- Debt not merely moved or renamed

## Failure Modes

The architecture must not be misread as:
- "Arango says it is solved"
- "The browser audit solved it"
- "The coding agent solved it"
- "The literature implies the theorem is proved"
- "The skill got a higher fitness score, therefore the theorem is closed"

None of those are enough.
