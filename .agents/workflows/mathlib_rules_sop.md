# Mathlib Rules SOP for This Repository

Downloaded references are stored under `external_refs/mathlib_docs/`:

- `README.md` — mathlib4 repository overview and build commands.
- `contribute_index.md` — contribution workflow and PR lifecycle.
- `contribute_style.md` — library style guide.
- `contribute_naming.md` — naming conventions.

## Required practices adopted here

### Before implementing

- Search Mathlib first; do not duplicate existing definitions/theorems.
- Discuss nontrivial library-shaped additions on Lean Zulip/mathlib channels when intended for upstreaming.
- Prefer small, self-contained changes over large bundled rewrites.

### File style

- Imports immediately after the header.
- Module docstring with title, main definitions/theorems, notation, and references where applicable.
- Keep lines at or below ~100 characters when practical.
- Use two-space indentation in declarations and structures.
- Avoid orphaned parentheses and unclear long proof terms.

### Naming

- Use descriptive lower-case theorem names with underscores.
- Name conclusions directly where possible (`map_zero`, `mul_assoc`, `foo_eq_bar`).
- Use `_of_` to encode essential hypotheses only when mathematically meaningful.
- Do not use names that suggest proof closure when the declaration is only a proxy (`*_valid`, `*_readback`, `*_certificate`, `*_witness`, `*_law`).

### Proof discipline

- Prefer theorem/lemma chains over large tactic blobs.
- Add reusable helper lemmas when a proof is repeated or conceptually meaningful.
- Keep proofs local and minimal, but never at the cost of hiding mathematical debt.
- `simp` lemmas and instances require extra care: add only when they are canonical and unlikely to loop or cause global regressions.

### Build and validation

For a touched file:

```bash
lake env lean path/to/File.lean
```

For dependency cache guidance from mathlib4:

```bash
lake exe cache get
lake build Mathlib.Import.Path
lake test
```

For this repo's proof-only gates:

```bash
python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
python3 tools/quality/check_no_hypothesis_mandate.py --root lean/InfoGeometry
python3 tools/quality/proof_only_mandate_gate.py
```

## Upstreaming posture

When code is intended to become a Mathlib contribution, make it independent of repository-specific physics/geometry naming and split it into the smallest reusable mathematical lemmas first.
