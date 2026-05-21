# BosonFermionFockIntertwiner

Lean module:

```lean
InfoGeometry.Canonical.BosonFermionFockIntertwiner
```

This module records the corrected level for the bosonization map, without
turning it into an isomorphism hunt.

It does not look for an algebra isomorphism:

```text
finite Cl(1,1) ≅ Heisenberg ≅ Virasoro
```

That is the wrong level.

It is also wrong to use origin language that suggests the finite atom itself
produces the Heisenberg/Kac-Moody/Virasoro hierarchy.  The finite atom can
supply local nilpotent/idempotent data; it does not contain mode labels,
normal ordering, or central cocycles.

Instead, it defines a representation-level packet:

```lean
FockLevelCurrentIntertwiner
```

with:

- a real linear map from a fermionic carrier into a bosonic carrier;
- an injectivity proof for that map, so commutator laws can be transported
  faithfully;
- fermionic and bosonic current operators;
- central operators on both carriers;
- an intertwining law for current operators;
- an intertwining law for central operators;
- the bosonic Heisenberg current law.

The main theorem is:

```lean
FockLevelCurrentIntertwiner.fermion_heisenberg_law
```

It proves that the fermionic current operators inherit the Heisenberg
commutator law through the faithful Fock-level current intertwiner.

Boundary:

This still does not construct the normal-ordered current

```text
J_n = sum_r :psi†_r psi_{r+n}:
```

from raw CAR modes.  That Wick/normal-ordering construction remains the next
constructive theorem.

Accepted level:

```text
faithful Fock-level current intertwiner
  + already-proved bosonic Heisenberg law
  -> transported fermionic Heisenberg law.
```

Rejected level:

```text
finite Cl(1,1) ≅ Heisenberg ≅ Virasoro.
```
