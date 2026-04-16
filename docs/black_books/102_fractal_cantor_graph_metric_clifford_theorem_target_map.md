# Fractal/Cantor, Graph-Metric, and Clifford Lanes: Bibliography + Theorem Target Map

## Executive summary

The safe repo statement is:

- fractal/Cantor constructions, graph-metric Dirac machinery, and split Clifford/Bott ladders can be compared in one program,
- but only through typed invariants and lawful intertwiners,
- not by collapsing them into a single unqualified ontology claim.

This chapter gives a curated bibliography and a theorem-target map aligned to current repo surfaces.

## Curated bibliography (research intake)

### A. Turkish Cantor/Clifford representation lane

1. Çelik, Koçak, Özdemir (2011), *Representations of Clifford Algebras on Function Spaces on the Cantor Set*, Adv. Appl. Clifford Algebras.  
   DOI: https://doi.org/10.1007/s00006-010-0235-7
2. Çelik, Koçak (2012), *A Fractal Representation of the Complex Clifford Algebra Equivalent to the Fock Representation*, Adv. Appl. Clifford Algebras.  
   DOI: https://doi.org/10.1007/s00006-011-0295-3
3. Çelik (2023), *A new approach to matrix isomorphisms of complex Clifford algebras via Cantor set*, Turkish Journal of Mathematics.  
   DOI: https://doi.org/10.55730/1300-0098.3346

These are the strongest direct matches for the “Turkish author + Cantor/fractal + Clifford representation” memory lane.

### B. Fractal-boundary Clifford analysis lane

4. Abreu-Blaya, Bory-Reyes, Bosch (2010), *Extension theorem for complex Clifford algebras-valued functions on fractal domains*, Boundary Value Problems.  
   EUDML entry: https://eudml.org/doc/228231

This is useful for “fractal domain -> operator/analysis constraints” targets.

### C. Graph-metric / discrete Dirac intake lane

5. Knill (2013), *The Dirac Operator of a Graph* (seminar/preprint surface).  
   PDF: https://people.math.harvard.edu/~knill/seminars/providence/providence.pdf
6. Chung (1997), *Spectral Graph Theory*, AMS.  
   DOI: https://doi.org/10.1090/cbms/092

These are intake references for graph-defined metrics and Dirac/Hodge-type discrete operators.

### D. Phase-space signed-lane context (connected but distinct)

7. Sellier (2015), *The Signed Particle Formulation of Quantum Mechanics*, Journal of Computational Physics.  
   DOI: https://doi.org/10.1016/j.jcp.2015.06.006
8. Wigner (1932), *On the Quantum Correction For Thermodynamic Equilibrium*, Physical Review.  
   DOI: https://doi.org/10.1103/PhysRev.40.749

This lane should remain translator-level relative to the doubled/Krein owner package.

## Status bands

- `REPO_THEOREM`: compiled theorem/definition in current owner/translator surfaces.
- `FORMALIZABLE_NEXT_OWNER_TARGET`: scoped theorem package to implement next.
- `EXTERNAL_RESEARCH_INPUT`: bibliography input not yet translated to owner declarations.
- `EXTERNAL_INTERPRETATION`: ontological claims that must not be promoted without owner proofs.

## I. Repo theorem anchors already available

- `REPO_THEOREM`  
  [operatorialIncidence_iff_projectorObstructionOperator_zero](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/TwistorOperatorialIncidence.lean:46)
- `REPO_THEOREM`  
  [bott_step_periodicity](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/BottPeriodicity.lean:134)
- `REPO_THEOREM`  
  [bottStep_headPair](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ClNNBottBridge.lean:32)
- `REPO_THEOREM`  
  [bottStep_tailLift](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ClNNBottBridge.lean:46)
- `REPO_THEOREM`  
  [annihilationShadow](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/SignedParticleBridge.lean:58)
- `REPO_THEOREM`  
  [classicalShadowOnRegularCore](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/SignedParticleBridge.lean:66)
- `REPO_THEOREM`  
  [idIntertwiner](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/QuantumPresentation.lean:77)
- `REPO_THEOREM`  
  [compIntertwiner](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/QuantumPresentation.lean:93)

## II. Formalizable next-owner targets

- `FORMALIZABLE_NEXT_OWNER_TARGET`:
  `FierzReadout` interface in split `Cl(n,n)`:
  channel decomposition into scalar/vector/bivector readouts with typed invariance obligations.
- `FORMALIZABLE_NEXT_OWNER_TARGET`:
  graph-Dirac presentation instance of `QuantumPresentation`
  (state space, observable action, generator, metric/phase readout contracts).
- `FORMALIZABLE_NEXT_OWNER_TARGET`:
  intertwiner package from Cantor/fractal function-space Clifford representation
  to finite matrix/Pauli realization for low-rank test cases.
- `FORMALIZABLE_NEXT_OWNER_TARGET`:
  Bott-ladder step functoriality:
  compatibility of representation intertwiners with `bott_step_periodicity`.
- `FORMALIZABLE_NEXT_OWNER_TARGET`:
  projector-controlled support transfer lemma from fractal-boundary extension data
  into the doubled/Krein support lane (`Preg/Pzero` boundary behavior).

## III. External research input (not yet owner-translated)

- `EXTERNAL_RESEARCH_INPUT`: Cantor/fractal Clifford representation papers listed above.
- `EXTERNAL_RESEARCH_INPUT`: fractal-domain Clifford extension theorem literature.
- `EXTERNAL_RESEARCH_INPUT`: graph Dirac and spectral graph references as discrete metric intake.

These should be consumed via typed translator modules, not imported as owner claims.

## IV. Explicitly external interpretation claims

- `EXTERNAL_INTERPRETATION`: “Clifford algebras are fractal sets producing spacetime.”
- `EXTERNAL_INTERPRETATION`: “Graph metric alone is a full quantum ontology.”
- `EXTERNAL_INTERPRETATION`: “Cantor representation proves physical discreteness by itself.”

All three remain non-owner until translated into precise declarations and proved in the Lean kernel.

