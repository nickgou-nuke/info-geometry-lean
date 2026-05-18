# External Theorem Hive

Status: local tooling, proposal authority only.

Purpose: expand Hive retrieval over Isabelle/AFP, Coq, Lean/mathlib, Logipedia/Dedukti, arXiv, and local Lean failure memory without changing the authority boundary.

Law:

```text
External proof library = theorem/proof intelligence source
Lean repo = proof authority
```

Foreign records may guide retrieval, symbol maps, adapter design, and proof reconstruction. They do not raise authority to `lean_checked`, `build_checked`, `audit_checked`, or `promoted`.

## Packet kind

`ExternalTheoremCandidatePacket` lives at:

```text
tools/schema/hive/ExternalTheoremCandidatePacket.schema.json
```

Required gates are always:

```text
lean_checked
build_checked
audit_checked
```

The main statuses are:

```text
discovered
normalized
matched_to_mathlib
requires_adapter
missing_in_lean
```

## Live source surfaces

Use live pages for lightweight discovery. Do not download large archives by default.

Observed source surfaces:

```text
http://logipedia.inria.fr/index.php
  Logipedia search index. Results link to /theorems/theorems.php?md=...&id=...&kind=...

http://logipedia.inria.fr/about/about.php
  Logipedia describes itself as proofs expressed in Dedukti, with exports to systems including Coq, Matita, Lean, PVS, OpenTheory.

http://logipedia.inria.fr/about/modules.php
  Module index: connectives, leibniz, logic, relations, bool, nat, div_mod, bigops, primes, cong, exp, fact, gcd, permutation, sigma_pi, fermat.

https://github.com/Deducteam/Logipedia
  Source repository. Important paths include src/dk2json.ml, src/export, src/json, theories, interoperability.

https://isa-afp.org/
  AFP entry index and search.

https://isa-afp.org/download/
  Stable archive download page. The full afp-current.tar.gz is intentionally not fetched by this lightweight harvester.

https://isa-afp.org/entries/Complex_Bounded_Operators.html
  AFP entry page with abstract, session, theory links under thys/Complex_Bounded_Operators/*.html.
```

## Live Logipedia page harvest

Harvest a Logipedia theorem detail page or search page without treating Dedukti/Lean exports as authority:

```bash
python3 tools/infra/external_theorem_harvester.py \
  --source logipedia-web \
  --web-url 'http://logipedia.inria.fr/theorems/theorems.php?md=primes&id=prime_to_lt_O&kind=theorem' \
  --query prime \
  --target-module InfoGeometry.Arithmetic.ExternalTheoremHive \
  --target-namespace InfoGeometry.Arithmetic.ExternalTheoremHive \
  --out artifacts/external_theorems/logipedia_prime_candidates.jsonl \
  --limit 10
```

The packet records:

```text
source_system = Logipedia
source_library = Logipedia/Dedukti
proof_transport_mode = dedukti
symbol_map includes: Dedukti proof object -> Lean theorem reconstruction guidance
```

## Live AFP entry harvest, no archive download

Harvest AFP entry metadata and theory names from an entry page:

```bash
python3 tools/infra/external_theorem_harvester.py \
  --source afp-entry \
  --web-url 'https://isa-afp.org/entries/Complex_Bounded_Operators.html' \
  --query 'bounded adjoint projection cblinfun L2 BLT Loewner' \
  --target-module InfoGeometry.OperatorAlgebra.ComplexBoundedOperators \
  --target-namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators \
  --out artifacts/external_theorems/afp_cbo_entry_candidates.jsonl \
  --limit 25
```

This records AFP session/theory surfaces as proposal packets. For theorem-level extraction from Isabelle source, use a local AFP mirror or extracted entry directory with the local harvest mode below.

## Local harvest example: Isabelle AFP bounded operators

```bash
python3 tools/infra/external_theorem_harvester.py \
  --source isabelle-afp \
  --input external/afp/thys/Complex_Bounded_Operators \
  --query "adjoint norm bounded operator projection Loewner BLT L2" \
  --source-library AFP/Complex_Bounded_Operators \
  --target-module InfoGeometry.OperatorAlgebra.ComplexBoundedOperators \
  --target-namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators \
  --out artifacts/external_theorems/cbo_candidates.jsonl \
  --split-dir artifacts/external_theorems/cbo_candidates
```

## Validate/ingest locally

```bash
python3 tools/infra/external_theorem_ingest.py \
  --input artifacts/external_theorems/cbo_candidates.jsonl \
  --out artifacts/external_theorems/cbo_candidates.validated.jsonl \
  --split-dir artifacts/external_theorems/cbo_validated \
  --fail-on-invalid
```

## Correspondence planning

```bash
python3 tools/infra/external_proof_correspondence.py \
  --candidates artifacts/external_theorems/cbo_candidates.validated.jsonl \
  --target-module InfoGeometry.OperatorAlgebra.ComplexBoundedOperators \
  --out artifacts/external_theorems/cbo_correspondence_plans.jsonl
```

## arXiv research guidance

arXiv is supported as a research/navigation source, not a proof source:

```bash
python3 tools/infra/external_theorem_harvester.py \
  --source arxiv \
  --query "Lean theorem proving Isabelle Coq proof translation Dedukti Logipedia" \
  --target-module InfoGeometry.OperatorAlgebra.ExternalTheoremHive \
  --out artifacts/external_theorems/arxiv_formal_transport_candidates.jsonl \
  --limit 10
```

## Lean reconstruction lane

For locally mirrored external corpora, keep the corpus under `external/<repo>` or `external_refs/<repo>` and search it by declaration index before rebuilding any theorem surface. Prefer a query/index workflow for already-proved theorems, then reconstruct the Lean-native theorem or adapter in this repo.

Repository-facing query helper:

```bash
python3 tools/infra/query_external_corpus.py admissible level --limit 20
```

The helper reads `external_refs/pyw/index.json` and `external_refs/pyw/keyword_index.json` and returns matching declarations for search-first triage.


The intended downstream chain is:

```text
ExternalTheoremCandidatePacket
  -> ExternalProofCorrespondencePlan
  -> TranslationPacket / TheoremCandidatePacket
  -> ExecutionIntentPacket
  -> LeanVerificationPacket
  -> BuildPacket
  -> AuditPacket
  -> PromotionDecisionPacket
```

For bounded-operator imports, prefer native Lean semantic reimplementation:

```text
foreign formal theorem
  -> mathematical role
  -> Lean/mathlib-native object
  -> small adapter API
  -> local Lean proof using existing facts
  -> locked lake build / audit authority
```

For CBO-013, the preferred route remains:

```text
Isabelle bounded multiplication on ell2
  -> L∞(μ) scalar multiplier on L²(μ)
  -> MeasureTheory.Lp heterogeneous scalar multiplication
  -> MeasureTheory.Lp.norm_smul_le
  -> ContinuousLinearMap wrapper
  -> Measure.count + Measure.ae_count_iff discrete bridge
```
