# LLM Frontier Protocol

This repository treats frontier packets as proposal artifacts, not proofs.

That means LLMs are useful in the loop, but only in a split role:

- creative lane: extend the frontier and propose missing bridges
- critical lane: reject weak proposals, minimize surviving candidates, and prepare quarantine-ready theorem sketches
- Lean lane: decide what is true

## Role Split

Use the creative lane for:

- missing morphisms between already existing semantic nodes
- candidate bridge lemmas
- small helper definitions when unavoidable
- attack plans for unexplored seams

Use the critical lane for:

- rejecting invented vocabulary
- rejecting thin bridges that reduce to `rfl`, direct forwarding, or tuple repackaging
- shrinking large speculative ideas into minimal theorem sketches
- deciding which candidates deserve quarantine materialization

Use Lean for:

- all proof authority
- all promotion decisions
- all final truth claims

## Workflow

1. Refresh the trusted frontier packet.
2. Generate the dual LLM prompts.
3. Submit the creative prompt to a proposal-oriented model.
4. Paste that output into the critical prompt and submit it to a Lean-aware review model.
5. Materialize only the surviving candidates in quarantine.
6. Run Lean validation.
7. Promote only proved results.

## Commands

Refresh the tracked docs and prompt pair:

```bash
python3 tools/update_repo_docs.py
```

Generate only the dual prompt pair:

```bash
python3 tools/generate_llm_frontier_prompts.py
```

The generated tracked prompts are:

- [frontier-prompt-creative.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/references/frontier-prompt-creative.md)
- [frontier-prompt-critical.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/references/frontier-prompt-critical.md)

## Safety Rule

The output of a creative model is never evidence.

The output of a critical model is never a proof.

Only Lean promotion makes a candidate part of the trusted theorem surface.
