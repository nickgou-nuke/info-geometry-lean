# Proof Alchemy Skill

Transmute proof debt (`sorry`) into kernel-checked Lean theorems via systematic
lemma decomposition and exhaustive toolchain search.

## The SOP (Standard Operating Procedure)

### Phase 1: Decompose

For each `sorry` in a theorem:

1. Write down the complete mathematical claim (extract from docstring if `True := sorry`)
2. Break into a linear chain of 3-10 SMALL lemmas L1 → L2 → ... → Ln
3. Each lemma must have a single, clear mathematical statement
4. Each lemma must be independently provable or citable

### Phase 2: Search — MANDATORY, exhaustive, before writing any proof

Search in this ORDER:

1. **Codebase toolchain** — run `query_dag.py`, `query_arango.py`, grep `artifacts/closure_debt_*.md`, `artifacts/ulamai/policy/obfuscation-patterns.txt`
2. **Mathlib cache** — `external_refs/atlas-lean/.lake/packages/mathlib/` and `lean_leansearch`, `lean_loogle`, `lean_local_search`
3. **External references** — `/tmp/auto_repo/proofs/`, `external_refs/gift-framework-core/`
4. **Artifacts** — `artifacts/dag/full_graph.json` (113K nodes), `artifacts/leantrail/graph_snapshot.json`, `artifacts/dag/causal_chiral_holes/`, `artifacts/dag/multiapex_supergraded_fivegraded_cones/`
5. **Web** — `WebSearch` for the mathematical theorem name + "proof" or "formalization"
6. **Web** — `WebFetch` the top 3 sources, extract the actual proof steps

### Phase 3: Download and Translate

For each lemma where a proof is found:

1. Download the proof source (arXiv PDF, MathStackExchange, textbook excerpt)
2. Translate to Lean-ready markdown with explicit steps
3. Cite the source in the Lean docstring

### Phase 4: Formalize

For each lemma, in priority order:

1. **Import existing** — if the lemma already exists in the codebase, `import` and use it
2. **Prove from existing** — if provable from imported theorems, write the proof
3. **State with sorry** — if genuinely open, leave `sorry` with lit reference and proof sketch

### Phase 5: Assemble

Wire all lemmas together in the main theorem. If all lemmas are proved, the
theorem is proved. If some remain `sorry`, the chain shows exactly which gap
blocks the proof.

## Anti-Patterns (FORBIDDEN)

- ❌ Replacing `sorry` with `trivial` (destroys information)
- ❌ Adding axioms to structures to hide debt (obfuscates what needs proving)
- ❌ Writing prose without decomposing into lemmas
- ❌ Searching only Mathlib and ignoring external_refs, /tmp/auto_repo, artifacts
- ❌ Proving from scratch when the lemma already exists in the codebase

## Success Pattern: HarmonicKMS.lean

**Before:** One `True := sorry` with no structure, 18 lines of prose in comments.

**After:**
- Main theorem references 5 existing codebase lemmas (all 0 sorry)
- Single `sorry` in `eckmann_discrete_hodge_betti1_zero` with:
  - Eckmann (1945) reference
  - arXiv:2512.05319 modern proof
  - Explicit statement: `betti1 = 0 → laplacian1 tc ψ = 0 → ψ = 0`
- Complete lemma chain documented in module docstring

## Toolchain Quick Reference

```
# Search codebase for a lemma name
grep -rn "theorem_name" lean/ external_refs/ /tmp/auto_repo/ --include="*.lean"

# Search ArangoDB graph exports
grep -rn "keyword" artifacts/dag/ artifacts/leantrail/ --include="*.json"

# Search closure debt catalog
grep -rn "keyword" artifacts/closure_debt_current.md

# Search obfuscation pattern map
grep -rn "keyword" artifacts/ulamai/policy/obfuscation-patterns.txt

# Query DAG graph
python3 query_dag.py "keyword"

# Search Mathlib local
lean_local_search "keyword"

# Search web
WebSearch "exact theorem name" + "proof"
```
