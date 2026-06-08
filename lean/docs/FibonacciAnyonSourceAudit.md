# Fibonacci Anyon Source Audit

This note records the durable audit map for the Fibonacci-anyon lane.  It is
separate from `CelikSourceAudit.md`: the Çelik/Koçak line supplies the
Cantor--Clifford/Fock and finite-metric/Gromov spine, while Fibonacci anyons
live in the braided-fusion-category and topological-quantum-computation spine.

## Sources Checked

- Michael H. Freedman, Michael J. Larsen, Zhenghan Wang, *The
  two-eigenvalue problem and density of Jones representation of braid groups*,
  Communications in Mathematical Physics 228, 177-199, 2002. DOI
  `10.1007/s002200200636`.  This is a primary density/universality source for
  the Jones/Fibonacci braid-representation lane.
- Chetan Nayak, Steven H. Simon, Ady Stern, Michael Freedman, Sankar Das
  Sarma, *Non-Abelian anyons and topological quantum computation*, Reviews of
  Modern Physics 80, 1083-1159, 2008. DOI `10.1103/RevModPhys.80.1083`.
  This is the standard review source for non-Abelian anyons, braid-group
  representations, Fibonacci anyons, and quantum-Hall realization proposals.
- N. Read and E. Rezayi, *Beyond paired quantum Hall states: parafermions and
  incompressible states in the first excited Landau level*, 1998/1999.  This is
  the source lane for `Z_k` parafermion quantum-Hall states, including the
  `k = 3` background commonly tied to Fibonacci anyon physics.

## What the Repo Currently Closes

The finite algebraic braid lane is already theorem-owned:

```text
golden scalar relations
  -> finite two-channel fusion matrix F
  -> diagonal exchange matrix R
  -> middle generator B = F R F
  -> Artin / Yang-Baxter relation R B R = B R B
```

Lean owners:

- `InfoGeometry.Canonical.FiniteFibonacciFusionMatrix`
- `InfoGeometry.Canonical.FibonacciParafermionAtoms`
- `InfoGeometry.Canonical.FibonacciParafermionFusionBridge`
- `InfoGeometry.Canonical.YangBaxterProof`
- `InfoGeometry.Fibonacci.HexagonCocycle`
- `InfoGeometry.Categorical.FibonacciBraiding`

The most concrete closed result is in `Canonical.YangBaxterProof`: the
repository proves the finite matrix braid relation

```text
R * B * R = B * R * B
```

for the explicit Fibonacci scalar package.  `Fibonacci/HexagonCocycle.lean`
also exposes mathlib's categorical braided Yang--Baxter coherence for any
`BraidedCategory`.

The real carrier lane is also finite and theorem-owned:

```text
real two-channel F matrix
  -> Majorana / Pauli decomposition
  -> real sl2 decomposition
  -> Krein adjoint signs
```

Lean owner:

- `InfoGeometry.Algebra.FibonacciParafermion`

This is a real Hestenes/Krein-compatible finite shadow of the Fibonacci
recoupling matrix.  It is not an analytic conformal-block construction.

## What the Repo Must Not Claim as Closed

The following are genuine proof debt unless and until separately formalized:

- density of the Fibonacci braid-group image in the relevant unitary group;
- Solovay--Kitaev compilation or arbitrary circuit approximation;
- a full modular tensor category instance with concrete objects, tensor
  product, associator, braiding natural isomorphisms, pentagon, and hexagon
  data all tied to the concrete matrices;
- conformal blocks, hypergeometric monodromy, or analytic continuation of the
  paper wavefunctions;
- physical realization of Fibonacci anyons in `Z_3` Read--Rezayi or
  parafermion lattice systems;
- fault tolerance, leakage-free universal gate sets, or measurement/readout
  protocols beyond the finite combinatorial interfaces already present.

## `Z3` Is a Related Realization Lane, Not an Identity

The finite Fibonacci category has two topological charges:

```text
1, tau
tau x tau = 1 + tau
```

That is not the same thing as an abelian `Z3` anyon theory.  The `Z3`
connection belongs to the parafermion/CFT realization lane:

```text
Z3 parafermion CFT or lattice model
  -> Read--Rezayi / engineered topological phase
  -> Fibonacci anyonic excitations
```

Lean should therefore keep these as bridge files with explicit hypotheses, not
as definitional equalities.  Existing files such as
`FibonacciParafermionAtoms` and `FibonacciParafermionFusionBridge` are correctly
finite: they expose algebraic atoms and real/complex matrix comparison, not a
physical derivation of Fibonacci anyons from a `Z3` phase.

## Clean Formalization Order

The theorem-safe dependency graph is:

```text
golden-ratio scalar lemmas
  -> two-charge fusion rule
  -> finite fusion-channel dimension counts
  -> finite two-channel F and R matrices
  -> F^2 = 1, det F = -1, B = F R F
  -> concrete Artin / Yang-Baxter matrix relation
  -> finite braid-word/projective readout interfaces
  -> categorical hexagon/Yang-Baxter coherence socket
  -> density/universality theorem target
  -> physical Z3 parafermion / Read--Rezayi realization target
```

Only the finite algebraic and categorical-coherence layers are closed in the
current Lean code.  Density, universality, and physical realization remain
explicit source-backed proof targets.

## Dictionary

```text
Fibonacci fusion side              Lean / operator side
---------------------------------------------------------------
topological charges 1, tau         `FibonacciCharge.one`, `.eps`
tau x tau = 1 + tau                finite fusion-output set
F-symbol                           finite `F` / `fibonacciFusionMatrix`
R-symbol                           diagonal `R` / `fibonacciRMatrix`
middle braid generator             `B = F R F`
Artin braid relation               `R * B * R = B * R * B`
hexagon coherence                  mathlib `BraidedCategory` coherence
universality / density             open theorem target
Z3 parafermion realization         open physics bridge target
```

## Audit Rule

When editing Fibonacci files, preserve this boundary:

- finite matrix equalities may be closed by computation and scalar lemmas;
- categorical Yang--Baxter may be imported from a real `BraidedCategory`;
- density/universality must cite and formalize the Freedman--Larsen--Wang/Jones
  representation theorem before being called proved;
- `Z3` parafermion language must be phrased as a realization or bridge target,
  not as the intrinsic definition of Fibonacci anyons.
