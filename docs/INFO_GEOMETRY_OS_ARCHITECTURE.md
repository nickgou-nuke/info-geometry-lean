# Info-Geometry OS: Formal Verification AI Architecture

This document is the master narrative architecture for the Info-Geometry OS
proof-search stack.

The system is not based on treating an LLM as an autonomous mathematician.  It
uses an LLM as a high-throughput heuristic generator inside a verified
environment:

```text
LLM generates candidates.
Lean checks truth.
Arango stores derived graph memory and audit overlays.
Python orchestrates retrieval, search, validation, and patching.
```

Lean remains the proof authority.  ArangoDB is navigation and memory.  Raw
InfoTree exports are compiler-memory sidecars, not proof evidence by
themselves.

## 1. Cognitive philosophy: the violin and the musician

The architecture separates four roles.

`The Violin`: the LLM, for example Qwen-35B behind vLLM.  It is a syntax and
pattern resonator.  It proposes Lean terms, tactics, proof sketches, and
repair candidates.

`The Acoustics`: Lean 4 elaborator, LSP, kernel, and final `lake build`.  These
are the physical constraints.  A candidate either elaborates and builds, or it
does not.

`The Score Library`: ArangoDB graph memory.  This includes dependency DAGs,
compiled-artifact joins, reference sidecars, SCC overlays, dominators, motifs,
process-flow defects, and loss-audited InfoTree overlays.

`The Musician`: the Python orchestrator.  It retrieves graph-conditioned
context, asks the LLM for candidate continuations, evaluates them through Lean,
updates search memory, and writes verified patches.

The design principle is:

```text
Graph memory guides.
LLM proposes.
Lean disposes.
The orchestrator records everything.
```

## 2. Trust boundaries

The architecture must preserve the repo's existing artifact doctrine.

`.olean` is the authority for compiled module and environment facts.

`.ilean` is the reference and location sidecar.

`raw_infotree_*` is a loss-audited elaboration-topology sidecar.  It persists
the runtime/server compiler-memory layer exposed through InfoTree and snapshots.
It is not the declaration dependency graph, not an SCC quotient, and not a
retrieval graph by itself.

The retrieval graph is built by joining multiple surfaces:

```text
.olean authority
  + .ilean references
  + declaration/dependency DAG exports
  + raw_infotree_* topology overlays
  + SCC/dominator/motif/process-flow overlays
  + attempt and diagnostic ledgers
```

The finite prime-lattice dictionary is separate from this analytic retrieval
graph.  Its core meaning is:

```text
prime-indexed Cantor lattice
  -> square-free finite-support vertices
  -> split-Majorana / Clifford packets
  -> local parity and global Möbius chirality
  -> finite Witten / Pfaffian readouts
```

Repository owner surfaces for that lane are:

- `lean/InfoGeometry/Arithmetic/SplitMajoranaPrimon.lean`
- `lean/InfoGeometry/Arithmetic/PrimeExteriorRepresentation.lean`
- `lean/InfoGeometry/Arithmetic/PrimeWittenCharacter.lean`
- `lean/InfoGeometry/Arithmetic/PrimeMajoranaPfaffian.lean`

The derived observability overlay for that lane lives under
`tools/observability/graph_overlay_toolchain/`; it is for navigation, wrapper
dedup, and audit reports only.

The current InfoTree layer should not be called fully lossless unless the
contract gates are satisfied:

```text
metadata.fully_lossless == true
raw_infotree_projection_leakage row count == 0
```

Until then, unknown compiler state remains explicit leakage, never fake zero.

## 3. The Logos Tidal Wave

The "Logos Tidal Wave" is operational context construction, not chat prompting.
The prompt prefix is a stable, graph-conditioned Lean context assembled from
verified and auditable artifacts.

For a target theorem, the prefix should contain:

```text
target declaration header
immediate imports
strict dominators
nearest dependency SCC
owner declarations and signatures
nearby simp/rw/theorem snippets
categorical motifs such as spans, cospans, diamonds, and commutative squares
current Lean goals
local context summaries
failed tactic exclusions for the same goal shape
```

The prompt should end at the proof frontier, usually with:

```lean
:= by
```

The model receives concrete Lean syntax and local goals, not raw De Bruijn JSON
as the main inference representation.  De Bruijn-invariant hashes and local
context structure belong in indexing, cache keys, and retrieval.  The model
should see the syntax it can imitate.

Prefix caching is mandatory for production inference.  The large context prefix
should remain stable across many MCTS expansions, while only the tactic suffix
changes.

## 4. MCTS proof-search loop

The orchestrator searches incrementally instead of asking for a full proof in
one shot.

`Selection`: choose a proof-search node with UCT or a related exploration and
exploitation policy.

`Expansion`: query Arango for dominators, owner declarations, motifs,
previously solved goal shapes, and failed tactic exclusions.  Build a stable
prefix and ask vLLM for candidate tactics or proof fragments.

`Evaluation`: inject the candidate through Lean LSP, collect diagnostics and
interactive goals, then optionally run a focused build for candidate closure.

`Backpropagation`: assign reward, update the MCTS tree, and write attempt
telemetry to graph memory.

Lean LSP is an interactive sensor.  The kernel and focused `lake build` are the
acceptance gate.

## 5. Reward and cache discipline

The negative cache key must include the proof state, not just tactic text.

A safe key shape is:

```text
targetDeclName
goalShapeHash or alphaHash
localContextHash
importsHash or environmentKey
tacticTextHash
diagnosticClass
```

A tactic can fail in one local context and succeed in another.  Over-aggressive
negative caching is proof-search self-sabotage.

Reward should distinguish syntactic progress from semantic progress.

Hard success:

```text
no goals
focused build passes
```

Strong progress:

```text
fewer goals
smaller expression complexity
goal shape matches a known lemma
generated subgoal has direct theorem retrieval support
```

Weak progress:

```text
changed goal but no simplification
introduced useful hypotheses
produced a useful local lemma
```

Negative:

```text
type mismatch
unknown identifier
timeout
goal explosion
looping or repeated shape without progress
```

## 6. Cold-start ingestion

Cold start has two distinct layers.

Dependency and declaration graph:

```text
Lean source and compiled artifacts
  -> declaration exports
  -> dependency edges
  -> SCC graph
  -> dominators, motifs, process-flow overlays
```

Compiler-memory topology:

```text
raw_infotree_* export
  -> topology-preserving InfoTree sidecar
  -> context, payload, mctx/lctx, leakage rows
  -> Arango descent verification
```

The raw InfoTree exporter must remain loss-audited.  Validation distinguishes
topology validity from full losslessness.

For real repository files, batch export should require corresponding `.olean`
files, impose per-file timeouts, validate per-file exports, and merge only
validated results.

## 7. Deployment model

`AI node`: runs vLLM and the selected tactic/proof model.  Prefix caching is a
hard requirement.

`Logic node`: runs ArangoDB, Lean workers, LSP sessions, focused builds, and
artifact validation.  It benefits from high single-core performance and fast
NVMe storage.

`Orchestrator`: coordinates retrieval, prompt construction, MCTS, Lean LSP,
build gates, patching, telemetry, and branch/PR creation.

Containerization should happen after the artifact contracts are stable:

```text
extractor contract first
ingestion contract second
retrieval contract third
orchestrator loop fourth
docker-compose after the interfaces stop moving
```

## 8. Patch and acceptance policy

The orchestrator must not commit directly to `main`.

Safe production flow:

```text
generate candidate
apply patch
run Lean LSP check
run focused lake build
run affected corridor build when required
write attempt telemetry
commit to agent branch
open PR or mark for human review
```

Direct commits are acceptable only on quarantined agent branches.

## 9. Core architecture statement

Info-Geometry OS is a proof-search architecture in which an LLM is used only as
a high-throughput heuristic tactic generator.  Lean remains the proof
authority.  ArangoDB stores graph memory extracted from dependency DAGs,
compiled artifacts, reference sidecars, and loss-audited InfoTree overlays.
The Python orchestrator retrieves graph-conditioned concrete Lean context,
queries the model through prefix-cached vLLM, evaluates candidates through Lean
LSP and focused builds, and records successes and failures back into graph
memory.
