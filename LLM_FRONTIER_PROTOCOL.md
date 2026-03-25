# LLM Frontier Protocol

Frontier work in this repository is proposal generation, not proof production.

## Role split

- creative lane: propose bridge statements, local decompositions, or new lower owners;
- critical lane: reject weak proposals, shrink claims, and isolate the smallest honest theorem surface;
- Lean lane: decide what is true.

## What counts as a good frontier proposal

A proposal is useful only if it:
- names real current owner modules;
- starts from existing repo data and hypotheses;
- can be tested by local build or semantic export;
- does not repackage an existing theorem under a louder name.

## Current tooling

Use:
- `tools/frontier/semantic_block_export.py`
- `tools/frontier/skynet_v2.py`
- `skills/info-geometry-repo/references/bridge-candidates.md`
- `skills/info-geometry-repo/references/bridge-reviewed-candidates.md`

Do not treat generated prompt packets or candidate lists as proofs.

## Policy link

For structural discipline while acting on a frontier packet, also use:
- [skills/lean-canonicalization-policy/SKILL.md](/home/goutev/LEAN4/info-geometry-lean/skills/lean-canonicalization-policy/SKILL.md)
