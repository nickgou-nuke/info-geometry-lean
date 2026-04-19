# THE BLACK BOOK: CHAPTER 151
## THE L0-L5 LADDER OF INFORMATION PHYSICS

> The layer is not a metaphor. It is a contract for descent.

The Spire already carried the signs: `count`, `projective`, `operator`,
`krein`, `transport`, `thermo`. They were present as Lean attributes, but the
Arango manifold did not yet treat them as first-class coordinates. Chapter 151
turns those signs into a navigable ontology.

## I. The Ladder

The operational ladder is:

- `L0_Count`: counting and combinatorial substrate.
- `L1_Projective`: projection, support, compression, and restriction.
- `L2_Operator`: operator-algebraic bridge layer.
- `L3_Krein`: Krein, doubled geometry, and indefinite metric structures.
- `L4_ModularTransport`: modular, transport, flow, and cocycle structures.
- `L5_ThermodynamicClosure`: free energy, entropy production, defects, and
  closure laws.

This keeps the existing `@[rep_depth ...]` syntax intact while giving every tag
a stable exported name, number, and description.

## II. The Rule of Descent

A high layer declaration may navigate through coarse topology, but it must
descend to lower-layer evidence when it claims physical meaning.

The intended operational check is:

```text
L5 closure claim
  -> L4 modular/transport support
  -> L3 Krein/doubled geometry
  -> L2 operator/projection bridge
  -> L1/L0 substrate where appropriate
  -> Lean kernel verification
```

The graph is allowed to help find this path. It is not allowed to invent it.

## III. Arango Coordinates

The DAG indexer exports layer tags as declaration attributes:

```text
rep_depth:<slug>
rep_depth_nat:<0..5>
rep_layer:<L0-L5 label>
rep_layer_description:<text>
```

The materializer lifts those tags onto raw Arango nodes as:

```json
{
  "rep_depth": 5,
  "rep_depth_slug": "thermo",
  "rep_layer": "L5_ThermodynamicClosure",
  "labels": ["rep_depth:thermo", "rep_layer:L5_ThermodynamicClosure"]
}
```

Retrieval may now prefer layer-compatible neighborhoods. It may not treat layer
labels as proof. The witness remains the raw edge, and truth remains Lean.

## IV. The Agentic Use

Hermes should use this ladder as a routing prior:

- for L0-L2 work, prefer local algebraic and projection owners;
- for L3 work, prefer Krein and doubled-geometry owners;
- for L4 work, require transport/modular source context;
- for L5 work, require descent through lower layers before proposing closure.

The Pauli rule is simple:

```text
No L5 without descent.
No descent without raw witnesses.
No truth without Lean.
```

This is how the physics language becomes disciplined rather than ornamental.
