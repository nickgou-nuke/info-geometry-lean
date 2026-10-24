# Open gaps and proof boundaries

Status: source-grounded reconciliation, 2026-10-24. This is a bounded ledger,
not a certification that every repository gap has been found or closed.

## Closure standard

A hypothesis, structure field, or axiom naming the desired conclusion does not
close a construction gap. A finite example proves that example; it does not
establish a growing tower or its completed limit. Lean owner statements and
kernel checks decide which claims have been proved.

The previous claim that all gaps were closed because they had been
"axiomatized or explicitly instantiated" was incorrect and is withdrawn.

## Inspected boundaries

| Surface | What the inspected source provides | Obligation not discharged by that source |
| --- | --- | --- |
| `proofs/DiracColimit.lean` | Self-adjointness conditional on `DiracColimitLimit`, and the constant identity tower `oneModeDiracData` / `oneModeDiracLimit`. | A nonconstant Clifford/Cuntz tower with proved compatibility and the intended colimit. The constant one-mode example does not discharge this requirement. |
| `proofs/KreinVacuumKMSBridge.lean` | Cancellation conditional on `DeltaRegularizedKMSContext`, including vanishing defect pairings for every tested pair. | Justification of that global assumption for the intended nontracial state. Ordinary matrix trace examples do not justify arbitrary Gibbs-state cyclicity. |
| `proofs/ZetaSpectralBridge.lean` | Finite spectral character sums; `InfiniteIwasawaAnalyticityLock` explicitly assumes `h_determinant_defect_zero`; `SpectralCriticalLineBridge` assumes the zero-to-critical-spectrum map. | Construction of the specified infinite determinant data and the spectral-zero identification. Conditional readouts do not eliminate these obligations. |
| `proofs/RiemannHypothesis.lean` | `hilbert_polya_hamiltonian_implies_RH` consumes a Hamiltonian schema. | The required spectral identification for the selected zeta function. No unconditional RH conclusion follows from this ledger. |

These statements describe the named owners, not a repository-wide absence
claim. Other owners must be traced before assigning implementation work.

## Native finite Gibbs construction already present

`lean/InfoGeometry/Canonical/FiniteMatrixGibbsFunctional.lean` constructs
`gibbsDensity` by Hermitian functional calculus, proves positivity and
invertibility, normalizes `gibbsFunctional`, and proves `gibbsFunctional_kms`
using the native inner algebra equivalence. Thus the finite density and
algebraic KMS construction requested in the older logical plan is already
implemented; it should not be rebuilt as a witness wrapper.

The precise finite centralizer boundary is now proved in
`lean/InfoGeometry/Canonical/FiniteMatrixGibbsCentralizer.lean`:

- `weightedTrace_commutator_zero_iff`: all weighted commutator pairings with a
  fixed X vanish exactly when D commutes with X; D may be singular.
- `trace_unit_right_annihilation_iff`: an invertible weight preserves matrix
  trace-pairing separation over any commutative ring.
- `weightedTrace_unit_defect_zero_iff`: all pairings of the modular defect
  vanish exactly when X is a fixed point of the native inner modular map.

The proofs reuse `TracialCARDensity.weighted_commutator_defect` and Mathlib
matrix trace separation. No state carrier or assumed separation field is added.
Independent source review and native locked QA passed; all four generated and
named declarations were axiom-clean, with zero owner warnings. Exact commands,
hashes and the axiom log are retained in `docs/FINITE_GIBBS_CENTRALIZER_KERNEL_RECEIPT.json`.
This closes this finite equivalence task, not the global continuum obligations.

## Finite Gibbs parity cancellation closed

`lean/InfoGeometry/Canonical/FiniteMatrixGibbsParity.lean` now proves:

- `gibbsDensity_commutes_of_commute`: a Hamiltonian symmetry commutes with
  its CFC exponential density.
- `gibbsDensity_parity_invariant`: a commuting involution preserves that density.
- `weightedTrace_gibbsDensity_odd_zero` and `gibbsFunctional_odd_zero`:
  an odd observable has zero unnormalized and normalized Gibbs expectation.
- `tiltHamiltonian_isHermitian` and `tiltHamiltonian_gibbs_switch_zero`:
  the existing diagonal Pauli parity and off-diagonal observable give the
  concrete case H = h • tilt2, for every real h and β.

Only H is assumed Hermitian; neither parity nor the observable requires that
assumption. The proof uses the existing Klein trace cancellation lemma and
never assumes global weighted-trace cyclicity. Independent semantic review,
locked native build, all-six-declaration axiom audit, and strict screening
passed with zero owner warnings. Evidence is retained in
`docs/FINITE_GIBBS_PARITY_KERNEL_RECEIPT.json`.

## Arbitrary finite seeds and algebraic-colimit positivity closed

`Canonical/GibbsParityTower.lean` proves CFC density and normalized Gibbs
transport along arbitrary `rawMap` transitions, odd cancellation after one or
many steps, and conditional colimit readout. The seed stage is arbitrary;
no backward Hamiltonian extension to stage zero is required.

`Canonical/FiniteSeedGibbsColimit.lean` reuses the existing
`normalizedDeltaWeightedFunctional (stageUnitToColimit k (gibbsDensityUnit H hH β))`.
Its five lemmas prove equality of transported density units, Gibbs readback
for every observable at any later stage, normalization, positivity for every
algebraic-colimit element, and odd cancellation at the seed injection.
Global positivity uses a common finite stage `max k j`. No new state carrier,
assumed positivity field, or scalar substitute is introduced.

Independent source audits, locked native builds, axiom audits (six actual
declarations for the tower owner and five for the seed owner), and strict
screens passed, with zero owner warnings. Evidence is in
`docs/GIBBS_PARITY_TOWER_KERNEL_RECEIPT.json` and
`docs/FINITE_SEED_GIBBS_COLIMIT_KERNEL_RECEIPT.json`.

A genuine two-level seed may start at stage 1. In contrast, strict Hamiltonian
propagation from stage 0 starts from a scalar and does not supply nontrivial
thermal dynamics. The explicit tilt seed now has its own nontraciality proof below.
The compatible Cstar stage-state boundary is now closed as recorded below.
Arbitrary interacting successor Hamiltonians, identification with total tensor
parity, and analytic KMS completion remain outside these results.

## Arbitrary-seed compatible Cstar states closed

`Canonical/FiniteSeedGibbsCStarStates.lean` proves star preservation and full
complex-order positivity of the existing global finite-seed functional. Its
restrictions construct native normalized positive `State` objects at every
matrix stage and the existing `CompatibleStateFamily`, with transition
compatibility derived from the colimit injections. Stages below the seed are
restrictions; no backward Hamiltonian extension is assumed.

Independent source review, locked native build, strict screening and an audit
of all 21 declarations passed with zero owner warnings. Evidence is retained
in `docs/FINITE_SEED_GIBBS_CSTAR_STATES_KERNEL_RECEIPT.json`. The represented
closure state construction is now closed as recorded below.

`Canonical/FilteredGNSVacuumReadback.lean` now proves that the native global
GNS vacuum has norm one and is independent of its stage, recovers each stage
expectation, and defines a continuous normalized functional on the existing
represented Cstar closure with proved positivity on star-squares. Its 36
declarations passed independent source review, locked native QA, axiom audit
and strict screening with zero owner warnings; evidence is retained in
`docs/FILTERED_GNS_VACUUM_READBACK_KERNEL_RECEIPT.json`. This statement does
not identify the raw algebraic colimit with its represented closure.

## Represented closure vacuum state closed

`Canonical/FilteredGNSVacuumState.lean` constructs the existing native `State`
on `representedCStarClosure` using Mathlib's spectral order. Positivity is
proved by square decomposition and the vector-functional square-positivity
lemma; normalization is proved from the unit vacuum. Every represented stage
observable recovers its prescribed compatible state, and the state is
independent of the chosen vacuum stage on the entire closure.

This construction accepts the compatible family supplied by
`finiteSeedCompatibleStageStates`. It supplies the previously assumed state
input of the represented-completion pipeline, with the spectral order retained
in its types. It does not identify the raw colimit with the represented closure
or prove faithfulness, analytic KMS boundary conditions, or interacting dynamics.

Independent source review, serial locked native build, strict screening and
all-38-declaration axiom audit passed with zero owner warnings. Evidence is in
`docs/FILTERED_GNS_VACUUM_STATE_KERNEL_RECEIPT.json`.

## Explicit finite nontracial Gibbs example closed

`Canonical/FiniteMatrixGibbsNontracial.lean` evaluates the native CFC Gibbs
density of every real diagonal Hamiltonian. For H = h • tilt2 it proves the
ordered matrix-unit expectation difference and its nonvanishing when β * h ≠ 0.
A nonconstant H alone remains insufficient at β = 0. No substitute density or
nontraciality hypothesis is introduced.

Independent source review, locked native build, all-six-declaration axiom audit
and strict screening passed with zero owner warnings. Evidence is retained in
`docs/FINITE_MATRIX_GIBBS_NONTRACIAL_KERNEL_RECEIPT.json`. Transport of this
concrete failure of traciality is now closed as recorded below.

## Explicit nontracial represented Gibbs state closed

`Canonical/FilteredGNSNontracialReadback.lean` proves that a supplied finite-stage
product inequality refutes cyclicity of the actual constructed vacuum state on
the entire native represented Cstar closure. The finite-seed specialization
uses the existing compatible Gibbs state family and matrix-to-Cstar equivalence.
Its transparent traciality definition reuses `NoncommutativeRenyi.IsTracial`;
it introduces neither state data nor a restricted testing domain.

`Canonical/TiltGibbsRepresentedNontracial.lean` supplies the finite inequality
for the stage-one Hamiltonian H = h • tilt2 under β * h ≠ 0. It proves both
algebraic-colimit product inequality and nontraciality of the represented
completed state, for every vacuum-stage choice. No nontraciality premise or
faithfulness assumption is added. This does not assert that every Gibbs seed
is nontracial, or prove analytic KMS dynamics or interacting limits.

Independent source review, serial locked native builds, strict screening and
axiom audits passed with zero owner warnings: 29 declarations in the transport
owner and five in the concrete specialization. Evidence is retained in
`docs/FILTERED_GNS_NONTRACIAL_READBACK_KERNEL_RECEIPT.json` and
`docs/TILT_GIBBS_REPRESENTED_NONTRACIAL_KERNEL_RECEIPT.json`.

## Bounded completed-operator self-adjointness closed

`Canonical/FilteredCompatibleOperatorSelfAdjoint.lean` compares finite-stage
vectors at a common upper stage and extends symmetry in both variables by
density. It proves self-adjointness of the existing bounded completed operator
from a compatible uniformly bounded stagewise self-adjoint family. It does not
assume exact finite-stage coverage of completed vectors. Construction and
uniform bounds of a growing Dirac tower remain open obligations.

Independent source review, serial locked native QA, strict screening and the
three-declaration axiom audit passed with no owner warnings. Receipt:
`docs/FILTERED_COMPATIBLE_OPERATOR_SELFADJOINT_KERNEL_RECEIPT.json`.

## Dense twisted-cyclicity extension closed

`OperatorAlgebra/DenseTwistedCyclicity.lean` extends a continuous readout's
algebraic twisted identity along a dense ring image in both variables. This
generic theorem assumes the algebraic identity; it does not by itself prove
KMS for a concrete state. Independent source review, locked native QA, strict
screening and the one-declaration axiom audit passed. Receipt:
`docs/DENSE_TWISTED_CYCLICITY_KERNEL_RECEIPT.json`.

## Finite-seed represented algebraic KMS boundary closed

`Canonical/FiniteSeedRepresentedKMS.lean` connects the two existing algebraic
colimits by an explicit star-algebra homomorphism, maps the native Gibbs density
unit and its inverse, and proves vacuum readback on the entire dense algebraic
image. Native algebraic twisted cyclicity then extends by continuity in both
variables to the actual represented vacuum State on the entire Cstar closure.
The finite seed is any Hermitian matrix and beta is any real parameter; neither
traciality nor completed twisted cyclicity is assumed.

Independent source review, serial locked native QA, strict screening and the
52-declaration axiom audit passed with no owner warnings. Receipt:
`docs/FINITE_SEED_REPRESENTED_KMS_KERNEL_RECEIPT.json`. This closes the bounded
algebraic boundary identity; analytic strip KMS, interacting Hamiltonian limits,
faithfulness, and raw-colimit identification remain outside its scope.

## Continuum discipline

Use proved finite-stage properties, explicit bonding compatibility, and the
repository-owned categorical inductive colimits. A constant finite example,
a scalar determinant field, or physical terminology does not substitute for
the intended transport construction. See `LOGICAL_GAP_CLOSURE_PLAN.md` for
historical obligations; its statuses also require owner-level reconciliation.

## Native matrix-tower GNS representation faithfulness closed

`Canonical/FilteredGNSMatrixFaithfulness.lean` derives injectivity of each
actual unital GNS stage representation from stage simplicity and the native
normalized nonzero vacuum. Direct-limit common-stage induction then proves
`algebraicColimitGNSRepresentation_injective` and `rangeAlgHom_injective`.
The concrete matrix specializations discharge simplicity using Mathlib and
the existing Matrix-to-CStarMatrix equivalence, for every compatible normalized
state family. No faithful-state hypothesis is introduced.

This supplies the existing faithful-completion owners' algebraic injectivity
input; it does not assert state-functional faithfulness or surjectivity onto
the completed closure. Independent semantic review, native locked build, all
six-declaration axiom audit and strict screening passed, with no owner warnings.
Evidence: `docs/FILTERED_GNS_MATRIX_FAITHFULNESS_KERNEL_RECEIPT.json`.

## Finite-seed represented real-time invariance closed

`Canonical/FiniteSeedRepresentedRealTime.lean` constructs the exponential
unitary of the actual represented seed Hamiltonian and its positive-time
conjugation action. It proves time continuity, identity and composition laws,
commutation with the mapped Gibbs density, and preservation of the existing
represented vacuum State for every Hermitian finite seed and real beta.
Invariance is derived from the already proved represented twisted cyclicity;
neither the flow nor its state invariance is assumed.

Independent semantic review, serial locked native build, all 79 declaration
axiom checks and strict screening passed. Evidence:
`docs/FINITE_SEED_REPRESENTED_REAL_TIME_KERNEL_RECEIPT.json`.
This closes real-time construction and invariance for finite seeds, not analytic
strip KMS, nontrivial motion, or the growing interacting Dirac obligation.

## Native tracial GNS bounded right action closed

`OperatorAlgebra/TracialGNSRightMultiplication.lean` derives star preservation
of the native PreGNS seminorm from trace cyclicity. Mathlib's existing left-action
bound then gives bounded right multiplication, extended by the existing
completion construction to the same GNS carrier. Representative readback and
the operator bound `norm (R_b) ≤ norm b` are proved. No faithful-state or
normalization hypothesis, replacement carrier, or assumed bound is introduced.

Independent source review, serial locked native build, all 21 declaration
axiom checks and strict screening passed. Evidence:
`docs/TRACIAL_GNS_RIGHT_MULTIPLICATION_KERNEL_RECEIPT.json`.
Adjoint and composition laws, the growing compatible commutator family, and
the coupled Dirac construction remain separate obligations.

## Native algebraic Fock new-head annihilation closed

`Clifford/FockTailHeadAnnihilation.lean` proves that contraction by the new
head coordinate vanishes on every spinor embedded by the existing `fockTailMap`.
Creation after that contraction also vanishes. The proof uses native Clifford
induction and the existing zero-head insertion, with no replacement carrier.

Independent source review, serial locked native build, the complete declaration
axiom audit and strict screening passed. Evidence:
`docs/FOCK_TAIL_HEAD_ANNIHILATION_KERNEL_RECEIPT.json`.
This supplies an algebraic compatibility ingredient for possible new-mode
couplings. The existing zero quadratic-form isometry is not a Hilbert isometry;
a Hilbert structure, adjointness, uniform bounds and the completed coupled
Dirac family remain open.

## Native tracial GNS self-adjoint commutator closed

`OperatorAlgebra/TracialGNSCommutator.lean` proves opposite right-action
composition, commutation with the existing left GNS action, and the right
adjoint law by completion density and traciality. It defines the actual
operator `L_H - R_H`, proves its dense representative commutator readback,
self-adjointness for self-adjoint H, and norm bound `2 * norm H`. The left
completed bound is derived from the native PreGNS bound, so no nonzero-state,
faithfulness, normalization, or assumed norm-bound premise is introduced.

Independent source review, serial locked native build, all 20 declaration
axiom checks and strict screening passed. Evidence:
`docs/TRACIAL_GNS_COMMUTATOR_KERNEL_RECEIPT.json`.
The growing Hamiltonian recursion, uniform all-stage bounds, bonding
compatibility and completed coupled Dirac construction remain distinct tasks.

## Native finite growing onsite Hamiltonian closed

`Canonical/GrowingOnsiteMatrixHamiltonian.lean` constructs the actual recursion
H(n+1) = concreteStep(H(n)) + w(n) tailZ(n) on the native matrix tower.
It proves Hermiticity, successor commutator compatibility, and nonzero
action on each fresh factor when its weight is nonzero. The tail embedding
is the actual reindexed identity tensor new-factor matrix.

Independent semantic review, serial locked native build, all 39 declaration
axiom checks and strict screening passed. Evidence:
`docs/GROWING_ONSITE_MATRIX_HAMILTONIAN_KERNEL_RECEIPT.json`.
Uniform summability bounds, GNS bonding compatibility and the completed
operator family remain distinct obligations. This onsite construction does
not establish an intersite coupled Dirac family.

## Native ordered Fock basis transport closed

`Clifford/FockTailExteriorBasis.lean` proves that the existing real exterior
basis is transported by native zero-head insertion to the basis indexed by
`S.map (Fin.succEmb n)`. Increasing enumeration preserves wedge order, with
no permutation sign. Empty occupancy and stage zero are included.

Independent semantic review, serial locked native build, all four declaration
axiom checks and strict screening passed. Evidence:
`docs/FOCK_TAIL_EXTERIOR_BASIS_KERNEL_RECEIPT.json`.
This remains algebraic basis transport. A Hilbert metric, Hilbert isometry,
creation/contraction adjointness and the completed coupled family remain open.

## Native all-index onsite commutator transport closed

`Canonical/GrowingOnsiteCommutatorTransport.lean` extends the actual successor
commutator identity along `concreteMap hij` for every `i ≤ j`. Induction uses
the native map recursion and the proved successor relation; no compatibility
hypothesis is introduced.

Independent semantic review, serial locked native build, all two declaration
axiom checks and strict screening passed. Evidence:
`docs/GROWING_ONSITE_COMMUTATOR_TRANSPORT_KERNEL_RECEIPT.json`.
The concrete completed GNS family and its uniform bounds remain separate work.

## Native completed tracial GNS commutator bonding closed

`Canonical/FilteredTracialGNSCommutatorTransport.lean` proves intertwining
of native completed GNS commutators from algebraic commutator transport.
Representative readback establishes equality on the dense PreGNS image;
continuity extends it to all completed vectors. No faithful-state assumption
or finite-representative coverage of the completion is used. A centralizing
increment provides a sufficient algebraic condition.

Independent semantic review, serial locked native build, all seven declaration
axiom checks and strict screening passed. Evidence:
`docs/FILTERED_TRACIAL_GNS_COMMUTATOR_TRANSPORT_KERNEL_RECEIPT.json`.
The concrete onsite application must discharge the algebraic premise and
assemble the compatible family with its independently derived uniform bound.

## Native uniform onsite Hamiltonian norm bound closed

`Canonical/GrowingOnsiteMatrixNorm.lean` transports the actual finite recursion
to Mathlib's CStarMatrix norm. The fresh tail is proved unitary with norm one;
native transition contractivity and scalar-action identification give the
finite absolute-weight sum bound. Absolute summability then gives one bound
for every stage. No uniform bound is assumed as an extra field.

Independent semantic review, serial locked native QA build, all 12 declaration
axiom checks and strict screening passed. Evidence:
`docs/GROWING_ONSITE_MATRIX_NORM_KERNEL_RECEIPT.json`.
Assembly and verification of the concrete completed GNS family remain separate.

## Native centralizing-increment criterion and boundary witness closed

`Algebra/CentralizingIncrement.lean` proves that exact commutator transport
through a unital ring homomorphism is equivalent to the increment centralizing
the embedded algebra. `Canonical/CuntzBoundaryCouplingObstruction.lean` proves
that every nonzero multiple of the actual two-site ZZ increment fails this
condition for the native identity-tail embedding, using the old-site switch.
The tensor matrices and their reindexing are the actual native carriers.

Independent semantic review, serial locked native builds, all 3 + 13 declaration
axiom checks and both strict screens passed. Evidence:
`docs/CENTRALIZING_INCREMENT_KERNEL_RECEIPT.json`.
This is an embedding-specific obstruction. Different vacuum embeddings and
asymptotic compatibility are not ruled out; coupled-family construction remains open.
