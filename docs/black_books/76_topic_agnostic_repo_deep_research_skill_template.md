# A topic-agnostic "repo deep research" skill template for Lean4 formalisation projects

## Why your "Einstein extraction" pattern generalises

The extraction you demonstrated (grouping everything "Einstein" into: core mathematical content, named theorems/defs, documentation, visuals, index/graphs, and "codebase philosophy") is already very close to a reusable methodology, because it mirrors how large Lean libraries stay navigable: they rely on (a) *auditable proof assumptions*, (b) *discoverable API surfaces*, (c) *dependency-aware modular structure*, and (d) *human-facing documentation that maps ideas to code*. citeturn2search9turn2search12turn3search0

Two pieces of Lean/Mathlib infrastructure make this particularly template-friendly.

First, Lean offers an explicit *assumption audit* mechanism: `#print axioms` prints axioms that a declaration depends on (transitively), and this includes detecting dependence on `sorryAx` (i.e., incomplete proofs). This gives you an objective "state of development" signal per theorem/definition. citeturn2search0turn2search4turn2search7

Second, the Lean ecosystem already has tooling intended to turn a repo into *browsable knowledge*: documentation generation (doc-gen4), import graphs, search tools (`#find`, Loogle), and rich export formats (lean4export) that can be repurposed as "LLM context packs". citeturn3search0turn3search1turn3search3turn3search10turn3search2

So yes: what you’re doing is not only a good template for investigating "Einstein"; it is a broadly reusable pattern for investigating **any topic** in a Lean4 repo, *and* it is a practical way to extract a formalised context suitable for agent reasoning and Socratic dialogues.

## A research workflow that scales to any topic

A robust "repo deep research" skill becomes repeatable when it always produces the same few artefacts, and when each step has a mechanical procedure behind it. The following workflow is topic-agnostic (replace "Einstein" with any concept/namespace/keyword list) and aligns with Lean’s own auditing and build model.

The core idea is to run the investigation in layers, from cheap lexical scans to proof-level audits and export-grade context.

### Lexical surface scan

This is the step you already executed well: case-insensitive keyword search plus targeted regex search (including compound forms like `Einstein-Kähler`, "anomaly-driven Einstein", etc.). This step is valuable because it discovers naming conventions and "semantic neighbourhoods" (where a topic appears in filenames, namespaces, docs, and graphs), which often predicts module boundaries and API surfaces.

In Lean projects, this should always include scanning for:
- names inside namespaces (e.g. `InfoGeometry.Canonical.*`-like prefixes),
- definitional keywords (`def`, `structure`, `class`, `theorem`, `lemma`, `axiom`),
- "scaffolding markers" such as `sorry` / placeholder proofs, because later maturity scoring depends on them. citeturn2search0turn2search9

### Semantic inventory extraction

After you have occurrences, the crucial "upgrade" is to extract *declarations* (what is defined/proved) and not just strings.

In Lean practice this is supported both interactively (searching) and structurally (documentation generation / export):
- `#find` can locate theorems/defs by type-pattern, which helps when you know the shape of a lemma but not its name. citeturn3search2turn3search6  
- Loogle provides searchable indexing of definitions/theorems and integrates with editor workflows, which is precisely the kind of affordance a future "research agent" can wrap. citeturn3search10  
- doc-gen4 generates HTML docs from a compiled Lean project, creating an API surface that is explicitly navigable. It can generate docs for code containing `sorry` as long as the project compiles. citeturn3search0

A topic dossier should record, for each relevant declaration:
- fully qualified name,
- short natural-language gloss,
- file/module path,
- dependencies (imports and/or referenced lemmas),
- "proof status" (proved vs depends on `sorryAx`), which comes from the axiom audit step below. citeturn2search0turn2search4

### Proof/axiom audit

This step is what turns "search results" into "state of development".

Lean explicitly recommends using `#print axioms` to audit what assumptions a declaration uses, transitively. This is an established method for detecting reliance on `sorry` and for spotting dependence on classical axioms (e.g. choice/extensionality) where relevant. citeturn2search0turn2search7turn2search4

If you want the template to be genuinely reusable, the dossier should treat the axiom audit as first-class metadata. Typical downstream uses include:
- prioritising which theorems count as "stable API" (no `sorryAx`) vs "experimental scaffolding",
- identifying "axiom hotspots" that block constructive or computational interpretations,
- supporting rigorous claims like "module X is fully formalised" in a way that is mechanically checkable. citeturn2search9turn2search0

### Dependency and architecture mapping

A topic isn’t just a list of theorems; it is a subgraph of the repo.

For Lean projects, there are standard ways to capture architecture:
- Lake standardises builds and dependency management, and `lake build` compiles Lean files into `.olean` artefacts, which is the foundation for all subsequent tooling (doc-gen4, export, etc.). citeturn2search1turn2search14turn2search5  
- Import graphs are a direct structural normal form for "what depends on what" at the module level. There is a dedicated tool (`importGraph`) for generating import graphs of Lake packages; it can emit Graphviz-friendly formats (and Graphviz is recommended for richer output formats). citeturn3search1  
- As a concrete example of the value of import graphs, Mathlib publishes an interactive import graph (node size indicating number of declarations), which demonstrates how quickly file-level dependencies become a navigational map for a library. citeturn3search25

Your own repo already mentions graph artefacts (e.g. `full_graph.json`, `edges.jsonl` in your excerpt). The template should treat these as outputs of the "architecture layer": they are exactly what enables an agent to avoid getting lost in a large codebase.

## Output contract for a reusable "Repo Deep Research" skill

A "skill" becomes reusable when it has a stable input/output contract. Below is a concrete contract that supports both human investigators and LLM/coding-agent workflows.

### Inputs

A minimal, topic-agnostic input record is:

- **Topic name**: e.g. `Einstein`, `Drazin`, `RadonNikodym`, `GNS`.
- **Lexicon**: keywords + regex patterns + namespace prefixes.
- **Entry modules**: optional list of "start here" Lean modules.
- **Questions**: optional research prompts (e.g. "What is the normal form?", "What is the foundational dependency?").

### Outputs

A strong default output set is three artefacts:

A **Topic Dossier** (`docs/research/<topic>.md`)  
Contains:
- narrative summary ("what exists, what is missing, what is intended"),
- inventory of definitions/structures/theorems,
- maturity notes (proved vs `sorryAx`-dependent), via `#print axioms`, citeturn2search0turn2search4  
- module map + import/dependency notes,
- links to generated docs pages (doc-gen4). citeturn3search0  

A **Lean Context Pack** (`Research/Context/<topic>.lean` plus optional exports)  
Contains:
- imports of the minimal set of modules needed to use the topic,
- `#check`/`#print` probes for key declarations,
- an optional "axiom report" section (or command output capture),
- optional export data: lean4export output for declarations relevant to the topic. citeturn3search3turn3search15  

An **Architecture Snapshot** (`docs/research/<topic>-graph.*`)  
Contains:
- import graph outputs (e.g. `.dot`, `.svg`, `.pdf`),
- optionally a machine-readable edge list, if you want to support downstream retrieval/graph reasoning. citeturn3search1turn3search25  

This contract is deliberately designed so a future agent can load the dossier as a "topic index", load the Lean context pack as a compilation-ready environment, and use the architecture snapshot to reason about where proofs and dependencies live.

## Implementation blueprint for a Lean4 repository

Even without adding heavy infrastructure, the Lean toolchain already gives you most of what you need; the template mainly needs to "wire together" established tools.

### Build and compilation gates

All downstream tooling assumes the project compiles. In Lean projects the compilation workflow is standardised by Lake: workspaces are built/updated via `lake build` / `lake update`, and compiled artefacts live in Lake’s build directories. citeturn2search1turn2search5turn2search14

A practical template usually defines two gates:
- **fast gate**: build only the topic context pack file (or a minimal target),
- **release gate**: full `lake build` + documentation + graph generation.

This mirrors how larger libraries treat "proof complete" vs "docs/artefacts complete".

### Documentation as a navigable API surface

doc-gen4 is explicitly designed to generate documentation for Lean 4 projects and integrates with Lake targets (the project must build; `sorry` is acceptable as long as compilation succeeds). citeturn3search0

In a template, doc generation serves two roles:
- human-facing: "browse the API by topic",
- agent-facing: "stable HTML pages that can be scraped/indexed for retrieval".

### Import graphs as an architecture primitive

The `importGraph` package is purpose-built for Lake import graphs, and recommends Graphviz when you want output formats beyond `.dot`. citeturn3search1

In a template skill, this step gives you:
- a module-level picture of the topic’s "home" and its upstream reliance,
- a quick check for architectural smells (e.g. high fan-in/fan-out, circular-feeling dependency patterns).

### Export for LLM context packs

lean4export provides a way to export elaborated Lean declarations into a plain-text format, and the recommended invocation pattern is to run it under `lake env` so that module search paths are correctly configured. citeturn3search3turn3search15

This matters for "agent skills" because:
- exports can be indexed by a retrieval system,
- retrieval can feed an LLM "exact statement text + dependencies" rather than lossy summaries.

This is closely aligned with how AI theorem-proving systems build training and retrieval datasets: LeanDojo, for example, explicitly focuses on extracting proof states/premises from Lean repositories and enabling programmatic interaction with Lean environments, in support of retrieval-augmented proving. citeturn2search3turn2search20turn2search16

## How this supports agent reasoning and Socratic dialogues

A topic dossier + context pack is not just documentation; it is a *dialogue substrate*.

To make this explicit, the skill template can require a "Socratic layer" section in each dossier that answers, mechanically, a fixed set of questions:

- **What is the minimal definition set?** (structures/classes/defs required before any theorem makes sense)
- **What are the canonical theorems?** (theorems that define the topic’s API)
- **What are the main equivalences/normal forms?** (statements that turn the topic into a simpler representation)
- **What are the failure modes?** (where `sorryAx` remains; where extra axioms enter; where definitions lack lemmas)
- **What is the shortest path to a nontrivial example?** (a tiny Lean snippet using the API)

The reason this is effective for an agent is that each question can be answered using the same artefacts:
- declaration inventory + doc pages for "what exists", citeturn3search0  
- `#find`/Loogle for theorem discovery when names are unknown, citeturn3search2turn3search10  
- `#print axioms` for "proof maturity / assumption budget". citeturn2search0turn2search4

This is also how you avoid "lyrical overfit" in agent reasoning: the agent is repeatedly forced back to *checkable declarations and their assumptions*, rather than relying on high-level labels.

## Measuring "state of development" in a way that stays honest

A reusable methodology needs a stable rubric. Lean’s tooling makes it possible to quantify maturity without subjective judgement.

A strong rubric typically combines:

- **Proof completeness**: declarations that depend on `sorryAx` are flagged as scaffolding (visible via `#print axioms`). citeturn2search0turn2search4  
- **Dependency sanity**: import graph position (how deep/highly-connected is the topic’s module cluster). citeturn3search1turn3search25  
- **Documentation coverage**: what appears in doc-gen4 output (and whether the docs build reliably). citeturn3search0  
- **Contribution/readability health**: adherence to community style and review norms (naming, structure, avoiding unnecessary complexity). citeturn2search12turn2search2  

This rubric aligns with how mature Lean libraries think about maintainability: "compiles without `sorry`" is treated as a meaningful correctness threshold, and review/documentation practices are treated as first-class library engineering concerns. citeturn2search9turn2search12  

In practice, a topic dossier can summarise state-of-development using a small, explicit "maturity block" (for example: **Green** = no `sorryAx` in core theorems; **Amber** = core API exists but depends on `sorryAx`; **Red** = names exist but little is proved / mostly axioms). The key is that each rating is backed by mechanically checkable evidence from Lean’s own audit command. citeturn2search0turn2search7

Finally, because you explicitly want this to be useful for future agents (including "me in the future"), the most important design constraint is: **every claim in the dossier should be traceable either to a declaration, to an axiom audit, or to a dependency/artefact output**. That is exactly the discipline that makes the template topic-agnostic and resistant to superficial narrative drift.
