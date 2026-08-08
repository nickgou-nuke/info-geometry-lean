# SageManifolds stack note: parameter bases and exponential algebra flows

It makes sense to add **SageManifolds/SageMath** as an optional witness layer for
the differential-geometric side of the project, but not as the proof kernel for
the hard de Rham/hypersurface-complement computation.

## Good uses in this repository

SageManifolds is well suited for explicit coordinate models of:

- parameter bases `B` for families/fibrations of algebras;
- local trivializations and transition functions of bundles of finite algebras;
- vector fields on parameter spaces, e.g. RG/modular/KMS flows;
- connections, curvature, torsion, vielbein/coframe calculations;
- matrix Lie algebra exponential flows `exp(tX)` generating local group orbits;
- frame changes, parabolic shears, affine log clocks, and Rindler/Weyl scaling;
- sanity checks for the differential-geometric meaning of Lean finite sockets.

Example intended interpretation:

```text
base manifold B: parameters such as beta, mu, q, theta, tau
fiber over b in B: finite algebra A_b, Clifford/Cuntz/CAR/TKK/etc.
connection: how generators/relations are transported with changing b
flow: exp(tX) on algebra generators or on frame/vielbein coordinates
```

This is especially appropriate for the repository's "algebra fibration over a
thermodynamic/modular parameter base" story.

## Interpretation layer: entropy, trajectories, and holonomy

As a **specification language** (not a proof claim), the project can read the
geometry as follows:

- `ln Q` = Boltzmann/Massieu entropy potential on the parameter base;
- `d ln Q` = differential score / Radon--Nikodym-type 1-form;
- modular Hamiltonian = generator of the flow that transports the family;
- de Rham 1-form cohomology = incidence/trajectory count of admissible flows;
- triple points = dual-node intersections in the spin-network / flow graph;
- Wilson holonomy = parallel transport around the inaccessible cone apex;
- chiral Dirac/Hodge operator = the signed transport operator on the dual network;
- `dlog`/log-barrier geometry = the Itakura--Saito/Bregman side of the same
  parameterized stack;
- the `2×2` matrix algebra picture = a local tessellation / fiber model for the
  chiral forward-backward transport rules.

This language helps organize the optional SageManifolds witness layer, but the
actual de Rham computation of the quadric complement still belongs to
Singular/Macaulay2/Oaku or a certified Dupont/Gysin discharge.

The concrete repository hook is:

- `proofs/non_iso_conf3_rank32_external_audit.py` now emits and runs
  `non_iso_conf3_rank32_sagemanifolds.sage` (under
  `proofs/artefacts/non_iso_conf3_rank32_audit/`) when `sage` is installed.

Reference pages:
- SageManifolds home page: https://sagemanifolds.obspm.fr/
- SageManifolds in Sage docs: https://doc.sagemath.org/html/en/reference/manifolds/index.html

## What it should not be used for

SageManifolds should not be treated as proving the actual cohomology of

```text
C^(2D) \ V(q(a) q(b) q(a-b)).
```

For that, use one of:

- Oaku--Takayama D-module computation;
- Macaulay2 `Dmodules`;
- Singular/Oscar for stratification plus a certified Dupont/Gysin model;
- SageMath as orchestration around Singular/Macaulay2, not as the core proof.

So the theorem-honest rule is:

```text
SageManifolds = coordinate/differential-geometry witness layer.
Lean = finite proof kernel.
D-module/Dupont/Gysin = actual de Rham computation socket.
```

## Suggested repository role

Add optional scripts under `proofs/` or `proofs/sage/`, for example:

```text
proofs/sage/algebra_fibration_base.sage
proofs/sage/parabolic_exponential_flow.sage
proofs/sage/modular_connection_curvature.sage
```

Each script should print an audit certificate, e.g.

```text
base dimension
coordinate chart names
connection coefficients
curvature/torsion simplification
exp(tN) group law check
frame/vielbein transformation law
```

These certificates can then be referenced by Lean socket records, without
turning analytic/geometric claims into hidden Lean theorems.

## Installation note

SageMath/SageManifolds is not currently installed in the local runtime checked
on 2026-06-18.  It can be installed via conda-forge if desired, but it is a large
dependency:

```bash
conda create -n sage-noniso -c conda-forge sage
```

Use it as an optional external witness environment, not as a mandatory build
dependency for `lake build`.
