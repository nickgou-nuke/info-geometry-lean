# raw_confabulation.txt formalization plan

Source:
- path: `raw_confabulation.txt`
- size: 33,514 lines / 2,016,599 bytes
- detected Lean code blocks: 135
- current role: mixed source containing rhetoric, mathematical ideas, theorem sketches, and embedded Lean fragments

## Goal

Turn the file into a theorem-distillation pipeline with strict separation between:
1. exact source preservation,
2. semantic mathematical partitioning,
3. closure/debt classification,
4. Lean extraction and repair,
5. optional Arango indexing as retrieval overlay only.

Lean remains proof authority. Arango or file indexes are retrieval/support only.

## Recommended folder layout

```text
raw_confabulation.txt

docs/raw_confabulation/
  00_source_index.md
  01_semantic_chunk_plan.md
  chunks/
    0001_<slug>.md
    0002_<slug>.md
    ...
  corridors/
    00_reflective_corridor_index.md
    01_owner_backed_corridors.md
    02_bridge_corridors.md
    03_open_debt_corridors.md
  theorem_packets/
    0001_<slug>.md
    ...
  lean_fragments/
    0001_<slug>.lean
    ...
  audits/
    duplicate_regions.md
    unsupported_claims.md
    code_block_inventory.md
    extraction_status.md
```

Optional retrieval overlay:

```text
handover/injections/raw_confabulation/
  manifest.json
  packets/*.json
```

## Phase 1: preserve source exactly

Do not rewrite the chunk files.
Each chunk file should be an exact contiguous slice of `raw_confabulation.txt`.
Only index files may interpret.

Outputs:
- `docs/raw_confabulation/00_source_index.md`
- `docs/raw_confabulation/chunks/*.md`

Chunking rule:
- split by semantic ridges, code-block boundaries, and repeated motif transitions
- preserve duplicates initially; deduplicate only in audit metadata, never by mutating source slices

## Phase 2: inventory and triage

For each chunk, classify content into one or more of:
- owner-backed mathematics already present in repo
- bridge-valid mathematical idea needing refactor
- speculative prose / overclaim / mythology
- embedded Lean worth extracting
- broken Lean / pseudocode
- duplicate or near-duplicate source region

Outputs:
- `audits/code_block_inventory.md`
- `audits/duplicate_regions.md`
- `audits/unsupported_claims.md`
- `audits/extraction_status.md`

## Phase 3: theorem-packet refactor

For each semantically coherent idea, create a theorem packet with fields:
- title
- exact source chunk references
- cleaned mathematical claim
- minimal hypotheses
- exact non-claims
- likely owner files
- likely translator/bridge files
- closure status: closed / conditional / open
- next Lean move

Important:
- remove rhetorical claims like “CPT proved” unless a native Lean theorem and correct hypotheses already exist
- downgrade analytic/topological claims to debt if the source only provides algebraic proxies
- separate finite toy algebra from actual modular/Tomita/operator closure

## Phase 4: Lean extraction lane

Treat embedded Lean in three buckets:

1. `kernel-valuable`
   - snippets that already express a real algebraic lemma and can be repaired into repo style

2. `mathematical-idea only`
   - code that encodes a valid intuition but with wrong abstractions or overclaimed interpretation

3. `discard as code`
   - code-shaped rhetoric whose theorem statement is mathematically false, too weak, or misinterpreted

For each extracted Lean fragment:
- store original under `lean_fragments/`
- annotate required imports
- identify missing assumptions
- test in isolation first
- only then map into existing owner/bridge modules

## Phase 5: repo-native formalization order

Recommended order of attack:

1. finite algebraic lemmas that are actually true
2. existing repo corridors with nearby owners
3. bridge theorems with exact readback interpretation
4. only later any analytic continuation / modular / AQFT claims

Avoid formalizing the strongest rhetoric first.
Prefer truthful local lemmas that compose.

## Phase 6: optional Arango overlay

Yes, Arango can help, but only after packets/chunks exist.
Use it as retrieval and dependency overlay, not authority.

Suggested node types:
- source_chunk
- theorem_packet
- lean_fragment
- repo_owner_file
- repo_bridge_file
- concept_tag
- debt_item

Suggested edges:
- `feeds`
- `mentions`
- `candidate_owner`
- `candidate_bridge`
- `refines`
- `contradicts`
- `duplicates`
- `blocked_by`

Minimal rule:
- every graph node must point back to exact line ranges in `raw_confabulation.txt`
- every promoted theorem packet must point to actual Lean owner files

## First-pass mathematical corridor list

Likely corridors visible from initial sample:
- Tomita / modular / Bisognano-Wichmann / mirror-time rhetoric
- Clifford / Cayley-Klein / Krein / Hestenes geometry
- Souriau / thermodynamic / Gibbs / partition-function bridges
- prime / zeta / anomaly / regularization claims
- Dirac / Majorana / spinor transport claims
- projective / Weyl / cocycle / modular flow claims

## Immediate cautions from the sample

The first sampled section contains a typical overclaim pattern:
- algebraic lemma in a ring
- then inflated into CPT / AQFT / modular-time interpretation

This should be split into:
1. a small noncommutative algebra lemma if true,
2. a separate debt note explaining why this does not by itself establish Bisognano-Wichmann or CPT.

## Suggested automation passes

1. detect all Lean code fences and extract line ranges
2. detect repeated long passages
3. build chunk boundary proposal around headings + code fences + motif changes
4. generate theorem-packet stubs
5. compile extracted Lean fragments in isolation
6. map surviving fragments to owner files

## Success criterion

Success is not “all prose converted to Lean”.
Success is:
- all source preserved,
- all major ideas partitioned into exact packets,
- each packet marked closed/conditional/open honestly,
- all usable Lean fragments isolated and tested,
- strongest reusable mathematics moved into proper repo corridors.
