# Canonical and quarantine semantics

This document defines semantic status terms for the repository.

These terms are not folder names.

## Canonical

`canonical` means a mathematical claim is promotable as repository mathematics.

A declaration or module is a canonical candidate only when its exported
mathematical claims satisfy all of the following:

1. Lean kernel checked.
2. Trust clean: no `sorry`, `admit`, unsafe leakage, unapproved axiom, or
   protected-region axiom dependency.
3. Non-vacuous: not merely `True`, not a trivial theorem wrapper, not only a
   projection of stored witness fields, and not a schema with no mathematical
   theorem content.
4. Owner rooted: depends on mathlib, a local proved owner theorem, or a checked
   constructive certificate.
5. Dependency clean: does not use quarantined, prognosis, graph-only, or
   diagnostic-only material as theorem authority.
6. Semantically stable: its statement says what the proof actually proves.

The folder `lean/InfoGeometry/Canonical/` does not automatically confer this
status.

## Quarantine

`quarantine` means controlled non-promotable mathematical holding status.

To be quarantined means:

1. The surface may remain in the repository.
2. It may be studied, searched, imported by explicitly unstable/research
   surfaces, and used as a source of hypotheses.
3. It must not be imported by public authority umbrellas or treated as theorem
   authority.
4. It must carry a reason that descends to current source evidence.
5. It must have an exit path: prove, split, rewrite, move to explicit
   hypothesis context, or retire.

Quarantine does not mean false.

Quarantine does not mean permanently noncanonical.

Quarantine does not mean “outside the `Canonical/` folder.”

Quarantine means the current evidence is not enough for mathematical
promotion.

## Prognosis / prima materia

`prognosis` or `prima_materia` means research material that may guide future
formalization but is not yet mathematical authority.

Examples:

1. Paper claim not yet formalized.
2. Arango/InfoTree/DAG proximity.
3. Retrieval hit.
4. Spectral, Hodge, Drazin, lightcone, or ranking diagnostic.
5. LLM prompt packet.

These may guide search. They do not prove the claim.

## Exact procedure for determining quarantine status

Quarantine status is assigned only after semantic descent through current
evidence.

### Step 1: Identify the claim surface

For each candidate declaration or module, record:

1. The exact Lean declarations involved.
2. The source file and line numbers.
3. The theorem-like claims exported by the surface.
4. The immediate imports and direct importers.

Do not classify from file path, folder, module name, or import name alone.

### Step 2: Run hard source audits

Use current checkout tools, not stale prose documents:

1. Lean build or elaboration for the target surface.
2. Frontier/trust checks for `sorry`, `admit`, `axiom`, `postulate`, unsafe
   leakage, and protected-region violations.
3. Constructivity audit for proof holes, axioms, `True`/`False` Prop constants,
   trivial theorems, universal `True` fields, zero-form surrogates, and
   projection-only theorem surfaces.
4. Mathfulness audit for vacuous or surrogate theorem-like declarations.

Hard source findings are evidence. They are not yet the final rewrite plan.

### Step 3: Use graph and InfoTree tools only as navigation

Use DAG, InfoTree, Arango, process-flow, Hodge, Dirac, chiral, Drazin, and
retrieval tools to answer navigation questions:

1. What depends on this surface?
2. Which owner theorem basin is nearby?
3. Is the flow regressive or boundary-bypassing?
4. Which raw declarations should be inspected next?
5. Is the InfoTree descent fresh enough to trust as provenance metadata?

These tools never prove mathematical content.

If graph descent is stale, partial, or failed, record that fact and do not use
the graph layer for promotion.

### Step 4: Descend to raw Lean content

For every suspicious declaration, inspect the exact source around the finding.

Classify the content, not the name:

1. `proof_hole_blocker`: contains `sorry` or `admit`.
2. `explicit_axiom_blocker`: introduces an unproved axiom or equivalent
   postulate.
3. `vacuous_or_surrogate_surface`: exports `True`, `False`, trivial theorem,
   universal `True`, or projection-only theorem as if it were mathematical
   content.
4. `diagnostic_only_surface`: only records graph/retrieval/spectral/ranking
   evidence.
5. `hypothesis_context_surface`: carries explicit assumptions currently (Native Closure Mandated); this
   may be acceptable, but it is not an unconditional theorem.
6. `owner_rooted_surface`: delegates to actual proved owner theorems or checked
   certificates.
7. `content_clean_by_this_audit`: no current audit finding; this is not itself
   promotion.

### Step 5: Choose the least destructive isolation action

Use the smallest action that prevents false theorem promotion:

1. If only a theorem wrapper is vacuous, split the wrapper into a separate
   expository or unstable file and keep real definitions where they are.
2. If the file mixes proved core definitions with speculative claims, split
   into:
   - proved owner/core file;
   - hypothesis-context file;
   - quarantine/prognosis file.
3. If an axiom is mathematically intended, replace it with an explicit context
   field or move the surface to quarantine until a proof exists.
4. If a proof hole exists, quarantine or rewrite the exact declaration; do not
   quarantine unrelated proved definitions by association.
5. If a claim is graph-only or diagnostic-only, keep it as an audit/training
   object and forbid theorem promotion.

### Step 6: Assign quarantine only with evidence

A surface is to be quarantined when at least one of the following is true and
cannot be immediately rewritten into a proved owner statement:

1. It has a proof hole.
2. It has an unapproved axiom or postulate.
3. It presents `True`, trivial theorem, universal `True`, or projection-only
   data as substantive mathematics.
4. It depends on quarantined/prognosis material as theorem authority.
5. It states an external paper or physics claim without a Lean proof,
   constructive certificate, or explicit hypothesis context.
6. It uses graph/retrieval/diagnostic evidence as if it were proof.

The quarantine entry must include:

1. Exact module or declaration.
2. Source file and line.
3. Finding category.
4. Why immediate rewrite was not done.
5. Intended exit path.

### Step 7: Validate the split

After isolation or rewrite:

1. Build the changed target.
2. Run constructivity/mathfulness checks on touched files.
3. Run quarantine import boundary checks.
4. Confirm public umbrellas no longer import non-promotable surfaces as
   authority.
5. Record remaining debt as prognosis/quarantine, not as theorem.

## Promotion rule

A quarantined surface may be promoted only when:

1. The offending declaration is proved, removed, or split away.
2. All remaining exported theorem claims are kernel checked and trust clean.
3. The claim has owner roots or checked certificates.
4. The graph/diagnostic layer is used only as provenance/navigation.
5. The public import path does not rely on unresolved assumptions.

Promotion is semantic. It is not caused by moving a file to a different folder.
