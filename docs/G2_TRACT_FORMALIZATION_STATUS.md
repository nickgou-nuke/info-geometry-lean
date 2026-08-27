# Formalization status of the cyclotomic/Galois tract

This note records the boundary between the prose tract in the attached
specification and the native Lean statements currently owned by the
repository.  Lean source and its kernel checks are authoritative.

## Closed native statements

- `G2CyclotomicPoincareFactorization.lean` proves the polynomial identity,
  its cyclotomic factorization, `P(2) = 189`, and the arithmetic identity
  `64 * 189 = 12096`.
- `G2GaloisCorrespondence.lean` defines the fixed-set/stabilizer maps and
  proves their antitone Galois connection, double-closure idempotence,
  zero/unit invariance, and closure under native addition and multiplication.
- `GaloisPeelingFiltration.lean` defines the finite stabilizer filtration,
  proves its antitonicity, and proves that its terminal stage is `⊥`.
- Existing native readback owners prove the stated conditional and
  unconditional `fullPeel` predecessors; they do not silently promote the
  remaining stabilizer reverse inclusion.
- `CyclotomicOperatorProjectors.lean` proves the general-ring `n`-potent
  projector identities, finite polynomial inverses for nilpotents, the
  characteristic-two geometric-sum specialization, and the `C₂` involution
  projector identities.
- `IwasawaOperatorTwinLoxodromic.lean` proves its explicitly parameterized
  rotor, Weyl-conjugation, loxodromic, twin-projector, and nonassociative
  derivation lemmas.  These are abstract ring/operator statements, not a
  construction of a KAN decomposition of the finite G₂ carrier.

## Statements deliberately not promoted

The prose labels several analogies as theorems, but the repository currently
has no native definitions and proof data for them:

- an Artin--Schreier/root-subgroup series for `nativeFlagStabilizer`;
- a field-theoretic Galois correspondence for the split-octonion carrier;
- the displayed orbit-size sequence;
- `nativeFlagStabilizer = unipotentSubgroup` without the residual readback;
- a concrete `G/U` identification or a group-order theorem from the
  cyclotomic arithmetic alone;
- Kummer, Bost--Connes, spectral, or Cuntz claims about the finite native
  carrier.
- An unconditional claim that the local staged source is present on remote
  `main`; remote provenance must be checked independently.

These are open specification edges, not assumptions.  In particular,
`P(2) = 189` is an arithmetic Weyl-polynomial result and does not itself
prove a quotient cardinality or a Bruhat partition.

## Development rule

Each new edge must introduce a native definition or an explicit witness and
then a kernel-checked theorem.  External CAS output may select witnesses, but
cannot supply propositions.  A missing edge is refined into its nearest
reachable theorem; it is never closed by `sorry`, `axiom`, cardinality
inference, or a renamed hypothesis.
