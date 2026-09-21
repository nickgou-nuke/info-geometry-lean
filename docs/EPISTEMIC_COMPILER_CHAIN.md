# Epistemic Compiler Chain

The repository treats research material as input to a proof-carrying
transformation pipeline.  The pipeline is a causal ordering of typed artifacts,
not a claim about hidden model reasoning:

```text
prima materia intake
  -> archetypal/causal normalization
  -> typed mathematical projection
  -> proof-carrying scheduling
  -> multi-agent candidate repair
  -> kernel-certified promotion
```

The formal carrier is
`InfoGeometry.MetaCompiler.EpistemicCompilerChain`.  Its `Phase` type records
the six stages and `Phase.precedes` is the rank order.  `Status` records the
research state:

```text
raw | speculative | stabilizing | corridor_ready | conditional | socket | debt | proved
```

Only `proved` can be passed to `promote`.  A successful promotion returns a
`CertifiedTheorem` containing the proposition, its owner, and an explicit Lean
kernel term.  The other statuses remain research metadata and cannot enter the
authoritative theorem surface.

The surrounding modules provide the larger checks:

- `MetaEpistemicCompiler` supplies prerequisite closure and alternative valid
  schedules;
- `Causal.CertifiedDependencyCompiler` and `Causal.ProofCarryingSchedule`
  supply dependency and evidence checks;
- `Meta/EpistemicPipelineTests` exercises rejection of malformed schedules,
  stale evidence, incomplete closure, and non-propositions.

The promotion boundary is therefore:

```text
raw artifact
  -> typed candidate
  -> scheduled candidate
  -> checked owner declaration
  -> Lean kernel proof
  -> CertifiedTheorem
```

Semantic proximity, graph adjacency, a CAS witness, or an agent proposal is
not a proof and does not cross this boundary.
