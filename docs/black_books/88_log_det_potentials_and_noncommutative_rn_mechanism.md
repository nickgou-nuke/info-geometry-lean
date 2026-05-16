# Log-det Potentials and the Noncommutative Radon-Nikodym Mechanism

## Executive Thesis

The correct noncommutative lift is not:

- `log (A * B) = log A + log B` as a primary operator law.

The correct primaries are:

- Radon-Nikodym chain rules,
- determinant/Jacobian multiplicative character laws,
- Connes cocycle chaining laws.

Additive log-potentials are derived scalar shadows after these multiplicative
laws are fixed.

## I. Classical Blueprint (Commutative)

In the commutative setting, Jacobians and Radon-Nikodym densities are the same
shape of object: multiplicative densities under composition.

- composition multiplies Jacobian factors,
- taking `log` converts multiplicative chain into additive cocycle.

This is the prototype for the noncommutative lane.

## II. Determinant as Abelianization

Determinants are multiplicative characters from nonabelian multiplicative data
to an abelian target.

- matrix-level: `det(AB) = det(A) * det(B)`,
- scalar potential shadow: `-log(det(...))` is additive under composition.

In noncommutative operator settings, this survives only through abelian
readouts (trace-like or determinant-like shadows), not as raw operator-log
additivity.

## III. Noncommutative RN Mechanism

For operator-algebraic state change, the primary chaining object is cocycle
data, not naive operator logs.

- state-to-state RN density chain at projective level,
- operator-level modular chain for `Delta`,
- Connes cocycle chain on the Type-III flow lane.

This is the noncommutative Jacobian chain rule.

## IV. Relative Modular Hamiltonian as Derived Lift

On the finite commuting diagonal lane, `K := -log Delta` is valid as a derived
operator and admits additive cocycle lifting.

In full noncommutative/Type-III generality, support/domain and cocycle
structure remain primary; additive Hamiltonian shadows are derived via those
owners.

## V. Repo Theorem Anchors (Current Proved Surface)

### A. RN and determinant chain lane

- `relativeDensity_state_chain`
- `relativeModularOperator_state_chain`
- `relativeModularVolumeShadow_state_chain`
- `relativeModularVolumePotential_state_chain`
- `jacobianDeterminant_chain`
- `connesCocycle_state_chain`
- `connesCocycle_state_chain_three`
- `realTypeIII_flowUnit_state_chain`
- `typeIII_connes_chain_package`

Owner file:

- `lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean`

### B. Delta-primary owner lane

- `relativeModularOperator`
- `relativeModularOperator_cocycle`
- `relativeModularVolumeShadow`
- `relativeModularVolumeShadow_cocycle`
- `relativeModularVolumePotential`
- `relativeModularVolumePotential_cocycle`

Owner file:

- `lean/InfoGeometry/Canonical/RelativeModularOperator.lean`

### C. Derived finite Hamiltonian lane

- `relativeModularHamiltonianOperator`
- `relativeModularHamiltonianOperator_cocycle`
- `relativeModularHamiltonianExpectation`
- `relativeModularHamiltonianExpectation_eq_readout`

Owner file:

- `lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean`

## VI. Methodological Law

The repository rule remains:

1. multiplicative/cocycle owner laws first,
2. additive potential shadows second,
3. narrative interpretation only after theorem ownership.

This preserves noncommutative current (Native Closure Mandated)y and prevents symbolic inflation.

## VII. Open Frontier (Not Yet Owner-Complete)

- full unbounded affiliated-operator `K = -log Delta` lane in Type-III owner
  generality,
- full Pedersen-Takesaki / Vaes-style operator RN lane as canonical owner stack,
- explicit continuous-core determinant/relative-Hamiltonian bridge as a stable
  owner surface.

