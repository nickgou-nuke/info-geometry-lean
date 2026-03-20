# LLM Debt Protocol

This repository treats debt packets as constructive replacement targets, not proofs.

The generated `debt-candidates.md` packet is report-only by design. It is not a
runner-ready materialization packet.

That means LLMs are useful in the loop, but only in a split role:

- creative lane: propose helper lemmas, proof decompositions, and local refactors for exact tracked debt targets
- critical lane: reject unsupported repair plans, shrink survivors, and prepare quarantine-ready theorem headers
- Lean lane: decide what is true

## Role Split

Use the creative lane for:

- small helper lemmas tied to a tracked debt surface
- constructive attack plans for exact theorem replacement
- theorem splitting when a bridge is too large to replace in one step
- explicit suggestions that a target should be deleted, renamed, or downgraded instead of "proved"

Use the critical lane for:

- rejecting invented helper lemmas or unsupported imports
- rejecting repair plans that still reduce to `rfl`, direct forwarding, alias transport, or packaging assembly
- shrinking large plans into minimal quarantine-ready theorem headers
- deciding which debt candidates deserve materialization first

Use Lean for:

- all proof authority
- all promotion decisions
- all final truth claims

## Workflow

1. Refresh the tracked debt audits and debt packet.
2. Generate the dual LLM debt prompts.
3. Submit the creative prompt to a proposal-oriented model.
4. Paste that output into the critical prompt and submit it to a Lean-aware review model.
5. Convert critical-lane output into a reviewed candidate packet that uses runner-parseable labels
  (`name`, `review verdict`, `review reason`, `quarantine recommendation`,
  `Lean-ready materialization sketch`).
6. Materialize only the surviving reviewed debt candidate in quarantine.
7. Run Lean validation.
8. Promote only proved replacements and regenerate the audits.

## Commands

Refresh the tracked audits, frontier packet, debt packet, and prompt pairs:

```bash
python3 tools/update_repo_docs.py
```

Generate only the tracked debt candidate packet:

```bash
python3 tools/generate_debt_candidates.py
```

Generate only the dual debt prompt pair:

```bash
python3 tools/generate_llm_debt_prompts.py
```

Run one quarantine cycle against a reviewed debt candidate packet (not the raw report-only debt packet):

```bash
python3 tools/run_optimization_cycle.py \
  --candidate-packet <reviewed-debt-candidates.md> \
  --candidate-index 0
```

Do not run `debt-candidates.md` directly through `run_optimization_cycle.py`.
That file is a report-only queue and does not carry a required reviewed
materialization sketch.

The generated tracked prompts are:

- [debt-prompt-creative.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/references/debt-prompt-creative.md)
- [debt-prompt-critical.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/references/debt-prompt-critical.md)

The tracked debt packet is:

- [debt-candidates.md](/home/goutev/LEAN4/info-geometry-lean/skills/info-geometry-repo/references/debt-candidates.md)

## Safety Rule

The output of a creative model is never evidence.

The output of a critical model is never a proof.

Only Lean promotion makes a debt replacement part of the trusted theorem surface.