# Super Souriau Fermion-Gas Context Packet

## Source Intake

Input prose: Bulgarian/English theorem-factory text describing a supergraded
Souriau ideal fermion gas:

- even sector: stress tensor and bosonic charge readouts;
- odd sector: supercurrent and supercharge readouts;
- super-geometric temperature split into even and odd components;
- grand-canonical density/generator as an even generator plus an odd source;
- Fenchel-Legendre/super-entropy reading;
- massless conformal/Weyl reading through supertrace-free stress.

## Alexandria Corpus

Requested arXiv/background corpus downloaded into `cache/`:

- `2104.12621`
- `2109.12806`
- `2204.02966`
- `2306.12662`
- `2310.18854`

Alexandria semantic ingest materialized:

- `digest/alexandria_documents.jsonl`
- `digest/alexandria_sections.jsonl`
- `digest/alexandria_chunks.jsonl`
- `digest/alexandria_entities.jsonl`
- `digest/alexandria_*_edges.jsonl`

Alexandria graph overlay materialized:

- `digest/overlay/alexandria_basins.jsonl`
- `digest/overlay/alexandria_basin_edges.jsonl`
- `digest/overlay/alexandria_entity_clusters.jsonl`
- `digest/overlay/summary.json`

Overlay summary:

- chunks: `1135`
- components: `934`
- canonical entities: `256`
- top basin representative: `Introduction`
- repeated defect tags: `tooling_overweight`, `rhetorical_drift`

Interpretation: the downloaded arXiv corpus supports the general
Fenchel-Legendre, Massieu, entropy, Hamiltonian, and thermodynamic-duality
background.  It does not by itself prove the full supergraded fermion-gas
claim.  The super-specific proof authority is repo-native.

## Arango/DGA Context

Faithful Arango query:

`SuperSouriauFermionGasBridge SuperMomentMapData FermionicCAROperatorPair
WeylSupertraceFreeStressContext superGrandCanonicalFockGenerator
odd_odd_superBracket_eq_CARBracket`

The retrieval pointed strongly into the supercharge/projector corridor,
especially `DrazinSupercharge`, but raw Lean descent showed that the direct
owner for the prose is narrower:

- `lean/InfoGeometry/Canonical/SuperSouriauFermionGasBridge.lean`
- `lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean`
- `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`
- `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean`

Bounded DGA run:

- components: `25947`
- quotient rows: `1184253`
- deduplicated quotient edges: `773050`
- cyclic residue: `0`
- bounded two-complex computed on radius-2 slice
- Hodge summary produced with bounded sparse truncation

Graph status: navigation/audit only.  The Lean owner files remain proof
authority.

## Repo-Native Mapping

| Prose claim | Repo owner |
|---|---|
| even stress/charge readouts | `SuperMomentMapData.stressTensor`, `SuperMomentMapData.bosonicCharge` |
| odd supercurrent readout | `SuperMomentMapData.supercurrent` |
| even/odd beta split | `SuperGeometricTemperature` |
| super Souriau action split | `SuperSouriauPairing.action_eq_even_add_odd` |
| grand-canonical Fock generator plus odd source | `superGrandCanonicalFockGenerator_eq_even_add_odd` |
| zero odd source reduction | `superGrandCanonicalFockGenerator_zero_odd_beta` |
| zero chemical potential reduction | `superGrandCanonicalFockGenerator_zero_mu` |
| odd-odd superbracket is CAR | `odd_odd_superBracket_eq_CARBracket` |
| even-even superbracket is CCR | `even_even_superBracket_eq_CCRBracket` |
| Pauli/Fermi behavior | `FermionicCAROperatorPair` and `cliffordConcreteFermionicCAROperatorPair` |
| supertrace-free Weyl stress | `WeylSupertraceFreeStressContext` |

## Formal Translator Move

The prose is exposed through:

- `claimS_superCoadjoint_stress_supercurrent_readouts`
- `claimF_superSouriauFermionGas_packet`
- `claimG_infiniteSuperCoadjointMetriplectic_packet`

`claimF_superSouriauFermionGas_packet` is a bridge theorem, not a new
supermanifold construction.  It packages:

- even stress and odd supercurrent readouts;
- even/odd Souriau action split;
- Fock grand-canonical generator plus odd source;
- odd-odd CAR channel;
- CAR nilpotence and mixed identity;
- Weyl supertrace-free stress and invariance.

`claimG_infiniteSuperCoadjointMetriplectic_packet` is the infinite lift.  It
works over arbitrary orbit and Lie/co-Lie carriers via
`FullCoadjointOrbitMetriplecticContext`, and packages:

- super-coadjoint stress and supercurrent readouts;
- orbit/Casimir entropy invariance supplied as an explicit proof;
- reversible entropy rate zero;
- dissipative/Onsager entropy production nonnegative;
- total entropy production reducing to the dissipative channel;
- Weyl covariance and supertrace-free stress supplied as explicit proofs.

## Remaining Debt

- No concrete `psu(2,2|4)` or super-Poincare representation is constructed.
- No supermetric variation theorem for a field-theoretic stress tensor is
  proved.
- No analytic super-Fenchel theorem on a genuine supermanifold is proved.
- No unconditional derivation of Fermi-Dirac statistics from arbitrary
  superalgebra anticommutators is claimed.
- No concrete infinite-dimensional super-orbit model is constructed; the
  infinite lift is a proof-carrying context interface.

The current closure is a proof-carrying translator surface over existing
Fock/CAR/Weyl-supertrace owners.
