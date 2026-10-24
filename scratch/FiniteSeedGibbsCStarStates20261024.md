# Native finite-seed compatible Cstar states

Uncompiled sandbox candidate. Independent AA and serial QA are required.
No live owner edits, tests, or builds performed by the author.

## Inputs and existing owners

- Arbitrary k, H : `CuntzMatrixTowerInstantiation.MatrixStage k`, H Hermitian,
  and beta : real. No extension of H below k and no compatible Hamiltonian
  family is assumed.
- `Canonical.FiniteSeedGibbsColimit`: exact existing normalized global
  functional, `finiteSeedGibbs_later_stage`, `finiteSeedGibbs_positive`,
  `finiteSeedGibbs_one`.
- `Canonical.CuntzMatrixAlgebraicStarColimit`: actual `Carrier`, `rawMap`,
  `stageInjection`, star/multiplication laws and `stageInjection_transition`.
- `Canonical.CantorBernoulliCStarMatrixTraceState`: existing `CStarMatrixStage`,
  `cstarConcreteMap`, `cstarConcreteMap_toMatrixStage`, `cstarMatrixInductiveSystem`.
- `Canonical.CStarAlgebraStateColimit`: actual native `State`, `State.restrict`,
  and `ContinuousStarInductiveSystem.CompatibleStateFamily`.
- `Canonical.MatrixGibbsCompatibleCStarState`: source pattern for positivity
  to monotonicity and the local CFC/order instances; no replacement carrier.

## Concrete constructions and proof delta

The stage linear functional is the composition of the existing global
`normalizedDeltaWeightedFunctional (stageUnitToColimit k (gibbsDensityUnit H hH beta))`
with `stageInjection n` and `CStarMatrix.ofMatrixStarAlgEquiv.symm`.

1. `finiteSeedGibbs_star`: common-max finite-stage readback proves global star
   preservation, using native `gibbsFunctional_star`.
2. `finiteSeedGibbs_nonneg_complex`: combines accepted real-part positivity
   with the zero imaginary part of the self-adjoint square's readout.
3. `finiteSeedStageFunctional_monotone`: positive elements of the native Cstar
   stage factor as star C * C; both existing maps preserve that factorization.
4. `finiteSeedStageState`: constructs a native positive map and proves its
   normalization from the existing global theorem.
5. `finiteSeedStageState_apply` and `finiteSeedStageState_transition`: exact
   identification and transition equality for every i <= j, even below k.
6. `finiteSeedCompatibleStageStates`: constructs the existing native compatible
   family with the transition proof, rather than assuming compatibility.

No new carrier or structure is declared. The private coordinate equivalence
only names the existing Mathlib equivalence. All proof fields of the existing
State and CompatibleStateFamily constructors are discharged in the candidate.

## Downstream boundary and QA

The family is ready as an input to the native filtered GNS owners. Finite state
continuity is already available via `State.toContinuousLinearMap`; no duplicate
boundedness machinery is added here. This candidate does not assert a completed
Cstar state, represented-vacuum readback, a uniform represented-operator bound,
or analytic KMS continuation.

Check the exact source under the shared build lock after AA, including common
stage induction, complex-order conversion, local CFC instances, coercions of
composed linear maps, and State.ext in the compatibility proof. No kernel or
axiom-clean claim is made for this candidate until independent QA supplies it.
