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
- producing quarantine-ready concrete sketches only for survivors that are explicit enough to build
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
5. Copy only critique-approved survivors into a reviewed bridge packet with explicit quarantine recommendations and concrete materialization sketches.
6. Materialize only the reviewed concrete sketches in quarantine.
7. Run Lean validation.
8. Promote only proved results.

## Commands

Refresh the tracked docs and prompt pair:

```bash
python3 tools/update_repo_docs.py
```

Generate only the dual prompt pair:

```bash
python3 tools/generate_llm_frontier_prompts.py
```

Run one quarantine cycle against a reviewed bridge packet with the conservative
proof driver:

```bash
python3 tools/run_optimization_cycle.py \
	--candidate-packet skills/info-geometry-repo/references/bridge-reviewed-candidates.md \
	--candidate-index 0 \
	--proof-attempt-command 'python3 tools/proof_driver.py --context {context_json}' \
	--proof-attempt-retries 1
```

The generated tracked prompts are:

- [frontier-prompt-creative.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/references/frontier-prompt-creative.md)
- [frontier-prompt-critical.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/references/frontier-prompt-critical.md)

The reviewed bridge packet used for concrete quarantine runs is:

- [bridge-reviewed-candidates.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/references/bridge-reviewed-candidates.md)

## Safety Rule

The output of a creative model is never evidence.

The output of a critical model is never a proof.

Only Lean promotion makes a candidate part of the trusted theorem surface.
