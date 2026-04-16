# Agentic Handover Policy (DGX Spark)

Effective date: **2026-04-15**

This document defines the production handover from human-led repository operation
to agentic operation for autotheory development.

It is a policy document. It does not override Lean. If this document and source
disagree, Lean source and build results are authoritative.

## 1. Mission

Run a disciplined dual-loop:

- **Exploration loop**: generate candidate structures quickly.
- **Closure loop**: admit only kernel-verified structures into the authoritative lane.

The purpose is high exploration throughput without ontology drift.

This handover is explicitly **multilingual in presentation, single-valued in
authority**:

- repo-native semantic language is preserved
- mathlib-native language is used aggressively as assembler language
- prose, Python, DAG artifacts, and black-book notes may assist discovery
- only Lean theorem surfaces close the contract

## 2. Authority Order

1. Lean kernel and build outcomes
2. Repository architecture grammar (`RepDepth`, adjacency, owner/translator/coherence/capstone)
3. Managed DAG policy gates (`dagRefresh`, `dagReports`, `dagDoctor`)
4. Human architecture decisions
5. Agent proposals and narratives

Any conflict is resolved upward in this order.

## 2.1 Exploratory Material

Exploratory material remains first-class research input but is never an
authority surface.

That includes:

- black-book notes
- multilingual docstrings
- Python or SymPy witnesses
- generated DAG narratives
- agent-generated synthesis prose

These may generate seeds, motifs, and candidate comparisons.
They do not certify ontology.

## 3. Operating Lanes

- **Lane A: Raw Intake (Exploration)**
  - fast hypothesis generation
  - may include unstable files
  - never treated as authoritative truth surface

- **Lane B: Stabilization**
  - owner/translator cleanup
  - import discipline
  - remove wrappers, placeholders, symbolic inflation

- **Lane C: Authoritative**
  - `InfoGeometry.All` and managed DAG products
  - requires green policy gates
  - only this lane is used for closure claims

### 3.1 Hermes Intake Subphase (Quarantined)

Hermes deep research is an intake surface inside Lane A, not a closure surface.

- output path:
  `quarantine/hermes_memory/research_packets/<timestamp>-<goal>.json`
- packet contract:
  `tools/schema/research_packet.json`
- packet validator:
  `python3 tools/infra/research_packet.py validate --packet <path>`

The packet must separate:

1. facts
2. interpretations
3. metaphors
4. formalization candidates

Only facts/interpretations may drive theorem candidates; metaphors are
exploratory scaffolding and cannot close claims.

## 4. Persona Assignment

| Agent | Primary role | Constraint focus |
|---|---|---|
| `NemoClaw` | Architect | layer placement, adjacency, owner boundaries |
| `OpenClaw` | Creator | candidate construction, bridge drafting, local synthesis |
| `DocClaw` | Librarian / Professor | bilingual docstrings, notation maps, blueprint-facing clarity |
| `ClawCode` | Caretaker | gates, cleanup, quarantine, release integrity |

All four are part of the production handover surface. No single persona may
self-certify closure.

## 4.1 Jung / Pauli Division Of Labor

The operating method is:

- **exploration may be Jungian**
- **closure must be Pauli**

In practice:

- raw symbolic generation is allowed in Lane A
- severe anti-inflation adjudication is mandatory in Lanes B and C
- attraction to an idea has no closure weight unless it yields a theorem,
  obstruction, invariant, or explicit comparison map
- dense bilingual docstrings are encouraged, but they remain explanatory
  pressure rather than theorem closure

## 5. Entry / Exit Criteria

### Lane A -> Lane B

Required:
- typed research packet from Hermes intake (`research_packet.json`)
- source-level rationale for ownership and layer placement
- no theorem-statement tampering
- explicit list of assumptions still unresolved
- explicit declaration of file role:
  owner, translator, coherence, or capstone
- NemoClaw architecture note must include a **Research Provenance** split:
  facts / interpretations / metaphors / formalization candidates
- if the module is intended to be bilingual or blueprint-facing, a docstring or
  adjacent note must name the repo-native formulation, the mathlib-native
  formulation, and the intended comparison surface

### Lane B -> Lane C

Required:
- research handoff gate:
  - `python3 tools/infra/check_research_handoff_gate.py --packet <packet> --nemoclaw-note <note>`
- `lake build InfoGeometry.All` green
- managed DAG cycle green:
  - `python3 tools/infra/dag_refresh.py`
  - `python3 tools/infra/dag_reports.py`
  - `python3 tools/infra/dag_doctor.py` with `fail=0`
- no unresolved symbolic placeholders admitted as closure
- explicit comparison theorem whenever two languages coexist in one stable lane

## 6. Anti-Inflation Contract

The following are prohibited in closure claims:

- claiming bridge completion from prose alone
- claiming unification from `True` wrappers or theorem-shaped placeholders
- treating unstable/raw intake modules as authoritative without stabilization
- allowing the mathlib presentation to silently displace the repo-native owner
- allowing bilingual modules to omit the translation/coincidence theorem

All “unity/coalescence” claims must point to explicit compiled bridge theorems.

## 6.1 Bilingual Module Contract

When a stable bridge module uses both repo-native and mathlib-native language,
it should contain or point explicitly to:

1. the repo-native statement
2. the mathlib-native statement
3. the formal comparison theorem
4. a note on what remains upstairs or does not descend

This is stricter than paper prose. Suggestive equivalence is insufficient.

## 6.2 Documentation / Blueprint Contract

For any stable bridge or coherence module intended to be read in more than one
mathematical register, the documentation layer should expose:

1. what is owned here
2. what is realized or translated here
3. the explicit comparison theorem
4. what remains upstairs or does not descend
5. optional references to local repo files or external mathematical literature

This layer is encouraged to be dense and bilingual.
It may use mathematical prose, notation maps, and references.
It may not claim closure independently of compiled theorem surfaces.

## 6.3 Dual-Implementation Contract

When two implementations of the same mathematical surface are intentionally
kept alive, the repository must treat them as:

1. one canonical owner/default API
2. one explicit alternative implementation
3. one compiled bridge theorem or bridge module
4. one downstream import route through the owner or the bridge

The following are prohibited:

- exporting both implementations as if they were coequal owners
- letting downstream files depend on both surfaces directly
- preserving two implementations without an explicit Lean comparison theorem
- hiding the alternative surface behind ordinary owner naming

The practical naming rule is:

- keep the ordinary exported name for the canonical owner
- mark the second surface with an explicit alternative or route suffix
- name the bridge theorem/module after equality, equivalence, or transport
  coherence

This is the stable way to preserve dual flexibility without semantic drift.

## 7. Quarantine Discipline

Raw or unstable modules remain outside Lane C until stabilized.

- Quarantine registry: `scripts/quality/quarantine_manifest.txt`
- Coverage gate includes only non-quarantined declaration-bearing files
- Quarantine is temporary and reviewable, not silent deletion

## 8. Handover Protocol (Daily)

Each cycle produces a short machine-auditable handoff:

1. **Architect note**: what file owns what, and why.
2. **Creator note**: what was introduced/changed.
3. **Librarian note**: docstring/blueprint coverage, notation alignment, and
   reference hygiene.
4. **Caretaker note**: gate results and unresolved defects.
5. **Artifact bundle**: updated DAG/report outputs with timing sidecars.

## 9. Date-Bound Activation

Starting **2026-04-15**, agentic infrastructure is the default operating mode.

Human override is allowed when:

- gate behavior is inconsistent with source reality
- architecture-layer decisions need explicit adjudication
- safety/sandbox policy needs update

## 10. Success Condition

The handover is successful if:

- exploration throughput increases in Lane A
- closure quality remains stable or improves in Lane C
- gate health remains green without relaxing policy rigor
