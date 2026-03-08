# The Grand Unification of the Physics of Information (Lean 4)

Raw facts:
- Lean files: `352`
- Lean LOC (all `.lean` files under `lean/`): `41,866`
- `sorry`/`admit` in `lean/`: `0`
- Full project check: `lake build -R`

## Core synthesis

- Thermodynamics: KMS control and RN-entropy barriers (`GrandSynthesis`).
- Geometry: Monge-Ampere / Ricci closure and Einstein-vacuum branch.
- Algebra: Clifford/Krein/operator-algebra bridges driving the same closure.

```bash
git clone https://github.com/nklgtv-nuke/info-geometry-lean.git
cd info-geometry-lean
```

Use any coding agent: Gemini CLI, Codex CLI, Claude Code, VS Code agent, Cursor, etc.

## Agent bootstrap prompt

```text
Read docs/keyword_index.md first.
Then run lake build -R.
Then map each major claim to exact theorem names and file paths.
Separate proved statements from physical interpretation.
```
