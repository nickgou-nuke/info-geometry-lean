# Entropic chiral de Rham dictionary

This note records a theorem-honest interpretation layer.  It is a dictionary of
intended meanings for existing finite Lean sockets and external symbolic audits;
it is **not** a claim that the analytic/operator-algebraic comparison has already
been proved.

## Core slogan

```text
d log Q around the inaccessible/forbidden cone
= logarithmic Radon--Nikodym / Jacobian potential differential
= modular Hamiltonian derivation / entropy-gradient clock
= parallel transport of the chiral Bogoliubov frame
= Wilson holonomy around the cone apex
= parabolic affine time on the dual Penrose spin-network tessellation
```

## Dictionary

Let `Q` denote the incidence/trajectory-count potential for the relevant node
configuration.  In the finite symbolic layer it is represented by the light-cone
or quadric barrier polynomial.

- `Q`: incidence/trajectory-count potential; inaccessible-cone barrier.
- `log Q`: Boltzmann/Shannon entropy potential, or self-concordant logarithmic
  barrier in the convex/interior-point reading.
- `d log Q`: de Rham 1-form around the forbidden cone; logarithmic
  Radon--Nikodym/Jacobian differential; residue/monodromy clock.
- `-log J` or `-log dν/dμ`: negative log Jacobian/Radon--Nikodym potential;
  finite witness for entropy production under change of frame/measure.
- modular Hamiltonian `K`: logarithmic generator of the modular/KMS flow;
  Bregman/Itakura--Saito log-generator in the information-geometric reading.
- `δ(A)=[K,A]`: modular derivation; infinitesimal chiral frame transport.
- Wilson holonomy: parallel transport of the chiral Bogoliubov frame around the
  inaccessible cone apex.
- chiral Dirac--Hodge operator: socketed analytic operator expected to couple
  de Rham cohomology, chirality, and Bogoliubov transport.
- Penrose / dual spin network nodes: triple-point incidence sites; forward and
  backward entropy-gradient flows propagate node affinities.
- `2x2` matrix algebra tessellation: local finite matrix tile/fiber carrying the
  chiral/Bogoliubov/modular frame data.

## Itakura--Saito / Bregman reading

For a positive potential `Q`, the logarithmic generator gives an
Itakura--Saito-type Bregman divergence.  The formal role is:

```text
entropy potential      φ = log Q  or  -log Q depending on barrier convention
Bregman divergence     D_φ(x,y)
modular generator      K ≈ log-density / log-Jacobian operator
derivation             δ(A) = [K,A]
clock form             d log Q
```

The sign is convention-dependent:

```text
d log Q = differential of log incidence/entropy potential
-d log Q = differential of convex barrier / negative log RN potential
```

Both conventions are already represented in the modular RN/Jacobian bridge by
explicit positive/negative log potential fields.

## Theorem-honest boundary

Compiled finite/proved layer:

- finite matrix/shear clock bookkeeping;
- modular derivation as a grade-preserving `g0` socket;
- additive parabolic clock laws;
- symbolic identities for `dlog Q`, Jacobians, and commutators in Python audits;
- finite tessellation/cooperad/rank bookkeeping.

Still socketed analytic layer:

- actual de Rham cohomology of the non-isotropic quadric configuration space;
- analytic residue/monodromy comparison;
- full Radon--Nikodym/Connes cocycle theorem;
- Tomita--Takesaki/Bisognano--Wichmann realization;
- Type III/KMS Hilbert-space representation;
- chiral Dirac--Hodge operator and Wilson holonomy as genuine operators;
- Penrose spin-network physical/geometric realization;
- proof that the `2x2` matrix tessellation is the actual algebra bundle/fibration
  over the chosen parameter manifold.

## Implementation target

This dictionary should connect to existing Lean/socket modules:

```text
ModularRadonNikodymJacobianBridge
ModularTimeDeRhamBridge
ModularParabolicTimeBridge
ChemicalPotentialDeRhamG0Bridge
BraidedCocycleWilsonEntropy
PenroseQuadricTopologySynthesis
LightConeConf3DeRhamCooperad / NonIsoConf3* sockets
```

Future SageManifolds scripts may model the smooth parameter base and the
exponential-map manifold of algebra frames, while Lean keeps finite claims and
D-module/Dupont/Gysin tools compute the actual de Rham complement.
