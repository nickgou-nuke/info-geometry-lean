# CliffordCompleteLatticeCurrentHierarchy

Lean module:

```lean
InfoGeometry.Canonical.CliffordCompleteLatticeCurrentHierarchy
```

This module packages the corrected hierarchy without overstating the proof.

It proves a theorem-level packet:

```lean
complete_lattice_current_hierarchy_packet
```

The packet contains:

- finite projection completion at a Cantor level;
- infinite projection completion;
- self-similar fixed-point completion;
- refinement/coarse-graining Galois connection;
- the finite split-null `Cl(1,1)` atom;
- the supplied source-side Heisenberg current law;
- the external Sugawara central action theorem.

Boundary:

The complete-lattice layer is order-theoretic. It organizes sectors and fixed
points. It does not by itself generate Heisenberg, Kac-Moody, or Virasoro.

The operator-algebraic substrate is represented by the finite doubled-real
`Cl(1,1)` nilpotent/idempotent atom and the projection-completion layer. The
AF/UHF inductive-limit language remains architectural here unless a separate
module supplies a kernel-checked inductive-limit construction.

For the matrix-facing local causal/Krein closure, use:

```lean
InfoGeometry.Clifford.SplitQ11CausalCone
```

Its documentation is:

```text
docs/SplitQ11CausalCone.md
```

Do not state that the local causal-cone algebra "grows into" the
Heisenberg/Kac-Moody/Virasoro hierarchy.  The finite atom is a local substrate;
the current/conformal objects are higher-level mode-indexed structures
available only through their own theorem-owner surfaces.

The current/conformal part of the packet requires supplied `heiOper`,
`heiTrunc`, and `hComm` data. In other words, the mode-indexed current family,
the local truncation condition, and the Heisenberg commutator law must already
be available before the external Sugawara API can be consumed.

The correct object to use is a representation-level current intertwiner, not a
finite-algebra isomorphism. See:

```lean
InfoGeometry.Canonical.BosonFermionFockIntertwiner
```

That module proves that a faithful Fock-level map which intertwines bosonic and
fermionic current operators transports the Heisenberg commutator law to the
fermionic current side. It is not a raw algebra isomorphism
`Cl(1,1) ≅ Heisenberg`, and it does not assert that the Fock carriers have
already been constructed as equivalent objects.

The module also exports readback theorems:

- `packet_refinement_coarse_galois`;
- `packet_finite_split_null_atom`;
- `packet_source_heisenberg_commutator`;
- `packet_external_sugawara_central`.

The remaining constructive theorem is still:

```text
split-Clifford/CAR fermion modes + normal ordering
  -> heiOper, heiTrunc, hComm.
```

Equivalently, the proved packet has the shape:

```text
finite Cl(1,1) atom
  + projection lattice completion
  + supplied mode-current Heisenberg law
  + external Sugawara endpoint.
```

It does not prove:

```text
projection lattice completion -> Heisenberg current law.
```

The accepted wording is:

```text
finite Cl(1,1) atom
  -> sector/projection substrate
  -> supplied mode-current representation data
  -> imported external Sugawara/Virasoro endpoint.
```

The rejected wording is:

```text
finite Cl(1,1) atom
  -> Heisenberg/Kac-Moody/Virasoro by recursive induction.
```
