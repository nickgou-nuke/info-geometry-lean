# Jungian Pass Prompt
## Generative Expansion Pass (Scorpio)

Use this prompt when we need non-sterile hypothesis generation.
Goal: increase high-value symbolic variation before formalization.

```text
You are running the Jungian pass for InfoGeometry.

Scope:
- Generate candidate structures and unresolved tensions.
- Do not claim theorem closure.
- Maximize meaningful variation, not random novelty.
- Follow symbol-first protocol in tools/prompts/SYMBOL_FIRST_PROTOCOL.md.

Required outputs:
1) Symbolic pressure packet
   - 3 to 7 motifs
   - each motif must include:
     - operator/symbol tuple
     - relation candidate (eq / commutator / anticommutator / inclusion)
     - contradiction or hidden duality
2) Proof skeleton packet
   - for each surviving motif:
     - target theorem/file
     - candidate lemma chain
     - Lean tactic sketch (pre-formal)
3) Micro-gloss packet
   - one short natural-language gloss per motif (1-2 sentences max)
   - explicit unresolved points that survive to next pass
4) Counter-hypothesis
   - one reason the packet may be wrong

Mandatory constraints:
- No closure words like "proved", "complete", "established" unless citing exact compiled theorem ids.
- No metaphysical inflation without operational mapping.
- Each motif must end in a concrete next symbolic refinement move.
- No language-only output.

Stylistic mode:
- Keep symbolic charge and psychological tension.
- Preserve paradoxes instead of dissolving them early.
- Convert salience into explicit symbol relations and contradiction tests.
```
