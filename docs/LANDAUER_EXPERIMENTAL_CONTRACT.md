# Landauer experiments: source and theorem contract

## Intake and source provenance

This continuation of the information-energy formalization uses three supplied
PDFs, read from the attachment bytes. The published reconstruction and Vopson
2022 modules remain prerequisite source. No physical interpretation is promoted
solely from a title, numerical fit, or successful compilation.

| Source | Exact intake | Mathematical role |
|---|---|---|
| M. M. Vopson, *The mass-energy-information equivalence principle*, AIP Advances 9, 095206 (2019), DOI 10.1063/1.5123794 | `095206_1_online.pdf`; SHA-256 `db021ac919c19c38f7af038a0e0967f112db64960c52b78b588a5afcc754ef94` | Shannon entropy and effective state count; the stored-mass interpretation is an additional conjecture. |
| A. Berut et al., *Experimental verification of Landauer's principle linking information and thermodynamics*, Nature 483, 187-189 (2012), DOI 10.1038/nature10872 | `nature10872.pdf`; SHA-256 `73ada75b4263b6a002f004b4823e150e7f466d2773586ba242fab5221ee64a9b` | Classical memory entropy loss and success-dependent heat bound. |
| A. Berut, A. Petrosyan, S. Ciliberto, *Information and thermodynamics: Experimental verification of Landauer's erasure principle*, arXiv:1503.06537v1 (2015) | `1503.06537v1.pdf`; SHA-256 `9554140c18a64048313597b7e22005bf76c18022e9735995f5b23f984daa75fb` | Finite mathematical consequences of conditional exponential-work averages, with explicit success/failure conditioning. |

Risk class: R4, finite probability, real analysis, and finite operator algebra.
Intended release: theorem-backed within the declared hypotheses; empirical
measurements remain external evidence; an intrinsic information rest mass and
a dynamical derivation of the fluctuation law remain open claims.

## Claim ledger and carriers

1. Use Mathlib's `Real.binEntropy p`, in natural-log units, for a classical
   two-outcome distribution. No new Shannon or probability carrier is introduced.
   The finite vector `![p, 1-p] : Fin 2 -> Real` connects it to the existing
   `InfoGeometry.Inference.FiniteGibbs.entropyOf` and relative-entropy owners.
2. Define the energy-valued erasure threshold
   `kB * T * (Real.log 2 - Real.binEntropy p)`. Its nonnegativity, extrema,
   monotonicity on the success range `[1/2, 1]`, and relation to relative entropy
   are mathematical consequences. A bound on actual heat additionally requires
   the stated entropy balance and bath relation `Delta S_bath = Q/T`.
3. For positive normalized finite weights `q` and a positive natural `N`, compare
   `Real.exp (N * entropyOf q)` with the genuine cardinality of `Fin N -> Data`.
   Equality requires uniform weights. For a nonuniform binary law with both
   outcomes possible, the single-copy effective count lies strictly between
   one and two and therefore is not a natural-number state count. This does not
   identify Shannon entropy with combinatorial support entropy for arbitrary laws.
4. Use native `Finset.centerMass` to prove the finite Jensen consequence of a
   bounded exponential work moment. Normalization, nonnegative weights,
   positive event masses, and positive inverse temperature are explicit.
   A success/failure partition reconstructs the total weighted mean. The
   conditional moments `(1/2)/p` and `(1/2)/(1-p)`, for `0 < p < 1`, imply the
   entropy-deficit work bound. They are assumptions at the physical interface,
   not conclusions about colloidal trajectories. Here `p` is success when the
   applied force stops, not automatically final-cycle success.
5. Retain arbitrary noncommuting matrices over a field for trace-reset duality.
   The forward map is exactly the existing native map
   `(Matrix.traceLinearMap n K K).smulRight sigma`. Its trace-dual observable
   is `trace (sigma * H)` times the identity. With `trace sigma = 1`, conservation
   against every matrix input is equivalent to `H` being a scalar identity.
   A concrete positive, normalized, noncommuting pair may have equal expectation
   for a nonscalar Hamiltonian, showing that one input's unchanged expectation
   is distinct from preservation for every input. No heat law follows from this
   matrix identity.

## Owner search and intended modules

| Owner | Existing content reused or distinguished |
|---|---|
| `Mathlib.Analysis.SpecialFunctions.BinaryEntropy` | Native binary entropy, endpoints, strict maximum, monotonicity. |
| `Inference.FiniteGibbsThermodynamicIdentity` | Generic finite Shannon entropy, uniform relative-entropy identity, entropy bounds, equality characterization. |
| `Inference.FiniteRelativeEntropy` and `FiniteRelativeEntropyEquality` | Normalized positive finite relative entropy and its equality case. |
| `Canonical.ThermodynamicChiralGraphCalculus` | Genuine finite forward/reverse path-law identity for the exponential of entropy production. |
| `Quantum.KrausBoundaryDuality` | General full-matrix Kraus trace duality and conserved-observable criterion; the new owner specializes the existing trace-reset map, without importing a quantum-channel implementation it does not use. |
| `Physics.InformationEnergy.TraceErasure` | Exact forward reset, splitting, kernel, multiplication defect, and noninjectivity. |
| `Physics.InformationEnergy.EnergyAccounting` | Existing first-law countermodel to forced stored-energy loss; reused in the interpretation, not restated as a new theorem. |

The bounded source search also inspected the repository's Jarzynski and
Landauer bridge files. A definition of an exponential average as its proposed
answer, or an assumption of a work bound, is not used as a proof of a physical
fluctuation theorem. Existing binary-entropy wrappers are not duplicated.

New owners under `lean/InfoGeometry/Physics/InformationEnergy/`:

- `BinaryErasure.lean`: finite entropy bridge, partial-erasure threshold, and
  entropy-balance equivalence with the heat lower bound.
- `EffectiveStateCount.lean`: effective-count versus actual finite-cardinality
  bounds, uniformity characterization, and binary nonintegrality.
- `Jarzynski.lean`: finite Jensen, genuine existing path-law specialization,
  success/failure partition, and conditional-work implications.
- `ObservableErasure.lean`: full-matrix trace duality, conserved observables,
  and a noncommuting positive-state example.

The dependency order is mathematical: existing entropy owners feed binary
entropy and state-count results; convexity and an explicit exponential-moment
hypothesis feed the conditional work theorem; the existing reset map and
nondegenerate trace pairing feed observable conservation. These are separate
branches until an explicit theorem connects them.

## Boundaries and source corrections

- The 2019 paper prints the entropy/heat inequalities in the reverse direction
  from its own total-entropy premise. The formalization uses the lower bound
  derived from that premise, and records the source discrepancy.
- Stored internal-energy change, supplied work, and heat delivered to the bath
  are distinct quantities. `Delta U = W - Q` is the chosen sign convention.
- `m = kB*T*log(2)/c^2` is an energy-to-mass conversion after an extra stored-energy
  identification. Neither the experiments nor these theorems establish that
  identification or its extension to elementary particles.
- Exact conditional work results use positive success and failure probabilities.
  The perfect-success endpoint is not substituted into a denominator-bearing
  conditional fluctuation identity.
- Finite sample/trajectory sums do not construct a stochastic differential
  equation, a continuous-path probability measure, a thermodynamic limit,
  complete positivity, or a quantum relative-entropy inequality.

## Validation and roles

The pinned Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` remain unchanged. Validation uses the
maintained source-closure checker, independent fresh compilation and declaration
axiom audit, source/semantic/static gates, and the installed staged-source hook.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted foundational
axioms; no proof holes, custom axioms, or unsafe proof shortcuts are introduced.

Generation: root and the isolated Jarzynski candidate author. Independent
source/mathematical audit: `paper_audit`. Independent final acceptance and fresh
kernel validation: `repo_survey`. Compiler and test commands remain serialized.

The pre-existing Atlas, HomotopyHypothesis, and GIFT dependency blockers are
checked and reported separately from selected module certificates. A draft PR
update is not a certificate for the complete root build or all imports in
`InfoGeometry.All`. Actual commands, results, hashes, and unresolved obligations
belong in the companion formalization report after verification.
