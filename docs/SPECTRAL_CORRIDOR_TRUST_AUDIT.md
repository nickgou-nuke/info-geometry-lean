# Spectral corridor trust audit

This note records the theorem-level boundary between the repository's established zeta/Apollonius geometry and the still-conjectural Hilbert--Polya/GUE corridor. Lean source and kernel checks remain authoritative.

## 1. Established geometric readout

The repository has genuine Apollonius/projective theorems. In particular, `Canonical/ApolloniusCriticalLineLeafBridge.lean` proves, for the repository's homogeneous Apollonius coordinates, that the projective critical-line condition is equivalent to the leaf coordinate `xi = 0` under the stated nonvanishing hypothesis.

This is a coordinate/geometric reformulation. It is not a proof that all nontrivial zeta zeros satisfy that condition.

## 2. Existing spectral-triple owner

`Quantum/SpectralTripleApollonius.lean` defines an `ApolloniusSpectralTriple` containing a linear operator `H_HP` together with a bilinear symmetry hypothesis `H_HP_symm`. The file proves formal symmetry of the derived Dirac operator and a commutator reduction.

The owner does **not** currently construct a densely defined unbounded self-adjoint Hilbert--Polya operator, prove essential/self-adjointness, determine its spectrum, or prove that its spectral parameters are exactly the ordinates of nontrivial zeta zeros.

Therefore the field name `H_HP` is notation/model data, not a Hilbert--Polya theorem.

## 3. First missing Hilbert--Polya edge

The first sound spectral edge is an operator-theoretic owner with an explicit domain and a genuine self-adjointness theorem, followed by a spectral correspondence theorem. Schematically:

```text
explicit Hilbert space H
-> explicit densely defined operator T with domain Dom(T)
-> T symmetric
-> T self-adjoint (or essentially self-adjoint with proved closure)
-> spectral theorem/readout for T
-> proved correspondence between Spec(T) and zeta-zero ordinates
```

The decisive missing theorem is not an Apollonius identity but a statement of the form

```text
Spec(T) = { gamma | zeta(1/2 + i*gamma) = 0 }
```

with all terms represented by genuine repository/Mathlib objects.

## 4. Trace-formula corridor

Repository reports and arithmetic overlay files contain theorem names connecting relative-trace, phase-shift, inverse-zeta, and completed-zeta channels. These declarations must be audited individually before use in a Hilbert--Polya trust chain. Historical `MajoranaPolyaHilbertSocket` material is explicitly associated with closure-debt/vacuity cleanup in the repository tooling and recovery archives.

Consequently, theorem-name presence in an overlay report is not by itself sufficient evidence that a full spectral trace formula has been proved from native hypotheses.

The required trusted bridge is:

```text
self-adjoint spectral operator
-> native trace/distribution object
-> proved trace formula
-> proved equality with a native explicit-formula owner
```

No socket, supplied equality field, or proposition-valued wrapper should substitute for this bridge.

## 5. Random-matrix/GUE boundary

`Canonical/PrimonGasGUE.lean` explicitly proves only the elementary conserved-charge statement obtained from commutation. It explicitly does not prove GUE spacing or a random-matrix statistical theorem.

Thus the valid logical status is:

```text
zero statistics / pair-correlation data
-> comparison with random-matrix predictions
-> GUE-type evidence
!= proof of the Riemann hypothesis
```

Any future GUE owner should state the finite/statistical observable, limiting regime, probability law, and convergence theorem explicitly.

## 6. Canonical dependency classification

### Theorem-level / geometric corridor

```text
zeta analytic structure
-> critical strip / critical-line predicates
-> Apollonius/projective critical-line reformulation
-> Apollonius cylinder / information-geometric models
```

### Open spectral corridor

```text
Apollonius/metriplectic spectral model
-> [MISSING] genuine self-adjoint Hilbert--Polya operator
-> [MISSING] spectrum = zeta-zero ordinates
-> [MISSING or audit-required] trusted trace formula
-> explicit formula
```

### Evidence-only corridor

```text
zeta-zero statistics
-> random-matrix comparison
-> GUE statistics/evidence
```

## 7. Development rule

Do not promote any of the following to theorem-level Hilbert--Polya evidence without the corresponding native proof:

- a field named `H_HP`;
- formal symmetry of an everywhere-defined `LinearMap` as a substitute for self-adjoint unbounded-operator theory;
- an Apollonius critical-line coordinate equivalence as a mechanism forcing zeros onto the critical line;
- theorem names from historical socket/overlay material without source-hypothesis audit;
- GUE terminology without a proved statistical limit theorem.

The next implementation should therefore start at the earliest missing operator-theoretic edge, not downstream at random matrices.
