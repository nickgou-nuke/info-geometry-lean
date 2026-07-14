# Spin Network Operational Machine Ledger

This note records the three-step operational dictionary in a theorem-honest
form.  It is a roadmap and ledger, not a claim that the physics interpretation
has already been proved in Lean.

## Machine Summary

The working slogan is:

1. Triangulate the `2 x 2` split-twistor/null-boundary algebra.
2. Attach discrete volume/readout data to the resulting Penrose/DAG cells.
3. Push flow through the network and read boundary/residue constraints from
   finite algebraic identities.

In the repository, the safe compiled core is narrower:

- the finite DAG-flow linker proves that a symmetric chiral word commutes with
  a directed edge under explicit swap laws;
- nilpotent square-zero hypotheses collapse the two chiral boundary channels;
- a thermodynamic gauge module records finite commutator and scalar-covariance
  identities;
- the on-shell residue bridge reads the BCFW-style boundary equality from the
  closed DAG-flow theorem.

## Verified Lean Surface

| Layer | File | Kernel-checked content |
|---|---|---|
| Thermodynamic finite flow | `lean/InfoGeometry/Topology/ThermodynamicGauge.lean` | `entropy_production` is the transition commutator; a supplied commutator equality identifies it with `d_ln_Q`; reciprocal scalar rescaling preserves the finite gauge word. |
| DAG/chiral linker | `lean/InfoGeometry/Topology/GrandUnificationLinker.lean` | `global_isometry_preservation`; plus/minus nilpotent boundary collapse; explicit-premise entropy alignment. |
| Residue/BCFW boundary | `lean/InfoGeometry/Projective/OnShellResidueBCFWBridge.lean` | `residue_bcfw` restates the closed linker theorem; no stored `ResidueBCFWInterface` witness packet. |
| Local dlog residue | `lean/InfoGeometry/Projective/KleinQuadricGrothendieckDeRham.lean` | Existing circle-integral readout for the local `dlog` pole model. |

## Interpretation Boundary

The following statements are active interpretations or roadmap targets, not
closed theorems in the current Lean kernel:

- split-twistor triangulations compute physical scattering amplitudes;
- Penrose spin-network volumes equal GUE-calibrated physical volumes;
- Kantor/TKK triple products replace all `6j` recoupling symbols;
- modular flow computes actual BCFW recursion or amplituhedron volumes;
- Wilson-loop traces evaluate a Bost-Connes or Riemann-zeta partition function.

Each of these can become a formal theorem only after a file supplies the exact
types, comparison maps, hypotheses, and analytic/convergence assumptions.

## Next Formal Obligations

1. `SplitTwistorTriangulationInterface`
   Define the finite triangulation carrier, the null-boundary predicate, and a
   map from braid/Delaunay flips to the DAG edge data used by
   `GrandUnificationLinker`.

2. `DiscreteVolumeCalibration`
   Separate finite volume labels from statistical/GUE calibration.  Prove only
   finite arithmetic/readout lemmas unless a real probability model is supplied.

3. `ModularFlowResidueComparison`
   Supply an explicit comparison between modular/KMS flow data and the
   `CausalNonequilibriumFlow` commutator.  This is the real owner for any
   theorem claiming `entropy_production = d_ln_Q`.

4. `BCFWResidueTheorem`
   Replace the current finite BCFW-style readout with an actual residue theorem
   only after compactification, divisors, residues, and factorization maps are
   formalized.

## Guardrails

Do not encode the remaining physics claims as fields named `*_certificate`,
`*_law`, `*_valid`, or propositions weakened to `True`.  Use explicit theorem
premises and keep analytic claims out of finite algebraic files unless their
formal assumptions are present.
