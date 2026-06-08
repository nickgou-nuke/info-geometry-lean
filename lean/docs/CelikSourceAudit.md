# Çelik--Koçak Source Audit

Local reference artifacts were downloaded under `docs/references/celik/`; that
directory is ignored by git, so this tracked note records the durable source map.

## Sources Checked

- Derya Çelik and Şahin Koçak, *A fractal representation of the complex
  Clifford Algebra equivalent to the Fock representation*, Advances in Applied
  Clifford Algebras 22(1), 39-47, 2012. DOI `10.1007/s00006-011-0295-3`.
- Derya Çelik, Şahin Koçak, Yunus Özdemir, *Representations of Clifford
  algebras on function spaces on the Cantor set*, Advances in Applied Clifford
  Algebras 21(1), 41-47, 2011. DOI `10.1007/s00006-010-0235-7`.
- Ayşe Hümeyra Bilge, Derya Çelik, Şahin Koçak, *Optimal embeddings of finite
  metric spaces into graphs*, Anadolu Univ. J. Sci. Tech. B 3(2), 133-147,
  2015. DOI `10.20290/btdb.87060`.
- Ayşe Hümeyra Bilge, Derya Çelik, Şahin Koçak, *An equivalence class
  decomposition of finite metric spaces via Gromov products*, Discrete
  Mathematics 340(8), 1928-1932, 2017. DOI `10.1016/j.disc.2017.03.023`.
- Ayşe Hümeyra Bilge, Derya Çelik, Şahin Koçak, *Gromov product structures,
  quadrangle structures and split metric decompositions for finite metric
  spaces*, Discrete Mathematics 344, 2021. DOI `10.1016/j.disc.2021.112358`.
- Derya Çelik, *Explicit determination of Gromov-product types of five-point
  metric spaces*, ESTU J. Sci. Tech. B 6(2), 185-192, 2018. DOI
  `10.20290/aubtdb.375635`.
- Ayşe Hümeyra Bilge, Derya Çelik, Mehmet Şahin Koçak, Arash Mohammadıan
  Rezaeınazhad, *Five point metric spaces: Gromov product structures,
  quadrangle structures and explicit parameterizations*, ESTU J. Sci. Tech. B
  11(2), 167-181, 2023. DOI `10.20290/estubtdb.1278467`.
- Derya Çelik, Şahin Koçak, Yunus Özdemir, Adem Ersin Üreyen,
  *Graph-directed sprays and their tube volumes via functional equations*,
  J. Fractal Geom. 4(1), 73-103, 2017. DOI `10.4171/JFG/45`.
- Derya Çelik, *A new approach to matrix isomorphisms of complex Clifford
  algebras via Cantor set*, 2023. DOI `10.55730/1300-0098.3346`.
- Salih Celik and Sultan A. Celik, *Differential Calculi on
  `Z₃`-Graded Grassmann Plane*, Advances in Applied Clifford Algebras 27,
  2407-2427, 2017. DOI `10.1007/s00006-016-0754-y`.
- Christensen and Ivan, *Wavelets and spectral triples for fractal
  representations of Cuntz algebras*, arXiv `1603.06979`.

## What the Papers Directly Support

The Cantor-Clifford papers support a conservative theorem lane:

```text
finite binary tree / cylinders
  -> Cantor boundary and ultrametric
  -> common-prefix depth / Gromov-product geometry
  -> finite Cantor endpoint/function-space data
  -> signed switch/tilt operators
  -> finite Clifford/Pauli representation
  -> infinite Cantor `L²(K)` representation socket
  -> inductive-limit / Fock-equivalence target
```

Lean owners:

- `InfoGeometry.Canonical.CelikKocakCantorOperators`
- `InfoGeometry.Canonical.CelikKocakPaperFormalism`
- `InfoGeometry.Canonical.FiniteCantorPauliMatrixBridge`
- `InfoGeometry.Canonical.CelikKocakInfiniteCantorCliffordFockSocket`
- `InfoGeometry.Canonical.CelikKocakCuntzFockBridge`
- `InfoGeometry.Topology.FractalCantorFockWitness`

The finite metric papers support the graph skeleton:

```text
finite metric space
  -> complete weighted graph
  -> Gromov products / excesses
  -> Delta-generic minimal product structures
  -> quadrangle structures and split metric decompositions
  -> optimal realization and graph moves
  -> small-n classification targets
```

Lean owners:

- `DAG.TwoComplex`
- `DAG.GraphHodgeBridge`
- `InfoGeometry.Categorical.Gromov`
- `InfoGeometry.Probability.Gromov*`

For the formalization order, this metric layer should be upstream of the
Clifford operator layer:

```text
binary words
  -> finite cylinders
  -> Cantor boundary
  -> ultrametric/common-prefix Gromov product
  -> finite-level function spaces
  -> switch/tilt operators
  -> Clifford relations
  -> Pauli tensor representation
  -> inductive/infinite Fock representation
```

Reason: switch/tilt operators act on binary coordinates; those coordinates come
from the symbolic Cantor tree; the Gromov product is the finite metric invariant
of the same branching/cylinder hierarchy.

The graph-directed sprays paper supports a graph-fractal analytic lane:

```text
Mauldin--Williams weighted directed graph
  -> graph-directed spray
  -> functional equation for inner tube volumes
  -> Mellin/zeta residue tube formula
```

The Cuntz spectral-triple paper supports the ambient operator-algebraic
category in which fractal Cuntz representations, wavelet decompositions, and
Cantor/Bratteli path-space spectral triples naturally coexist.  It does not
identify the local repo's Cuntz clock with a KMS flow by itself.

The Salih Celik lane is separate:

```text
`Z₃`-graded Grassmann plane
  -> covariant differential calculi
  -> Grassmann--Heisenberg algebra
  -> graded Yang--Baxter `R`-matrix
```

That material may become relevant to graded quantum/super differential
calculus, ternary nilpotence, or Yang--Baxter sockets, but it is not the source
for the Cantor/Fock/Gromov spine.

## Core Dictionary

The clean formal dependency for the Derya Çelik / Koçak line is:

```text
fractal / metric side                 operator / Clifford side
----------------------------------------------------------------
Cantor point                          infinite binary occupation string
cylinder set                          finite occupation prefix
finite Cantor approximant             finite Clifford module
common prefix / Gromov product        mode hierarchy / branching depth
self-similar shift                    creation/annihilation-type operator
tilt and switch on bits               Pauli matrices / Clifford generators
Cantor `L²` space                     fermionic Fock Hilbert space
```

The finite Gromov-product layer is therefore not merely decorative.  It records
the same common-prefix hierarchy that the Cantor-set Clifford representation
uses as its cylinder/mode structure.

## What Remains Genuine Proof Debt

The reviewed papers do not, by themselves, close these repo claims:

- analytic `O₂` / CAR / infinite Clifford completion equivalence;
- construction of an actual `L²(K)` Hilbert completion inside Lean;
- a unitary equivalence with the classical Fock representation;
- Cuntz `K_0(O₂)=K_1(O₂)=0`;
- uniqueness, contraction, CPTP, or continuous modular-flow classification for
  the Cuntz map;
- Cayley compactification or KMS thermodynamics from finite Gromov products.

Those should remain sockets, witnesses, or explicitly conditional bridges until
the required hypotheses are formalized.

## Naming Correction

The verified Cantor/Fock/Gromov source trail here is Derya Çelik with Şahin
Koçak and collaborators.  Salih Celik is a different source lane, currently
verified here for `Z₃`-graded Grassmann/differential calculi and graded
Yang--Baxter structures.  Do not attribute the Cantor/Fock/Gromov papers to
Salih Celik.
