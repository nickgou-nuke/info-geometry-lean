# QMS purification ledger

Scope: theorem-honest purification of vacuous or overclaimed Lean surfaces.

Policy:
- Orchestrator performs discovery and writes exact typed theorem statements.
- Proof agents receive only fixed Lean targets and prove proof bodies/helper lemmas.
- No theorem is promoted from prose, witness fields, `False := sorry`, `Prop := True`, or vacuous examples.
- Remaining semantic gaps stay explicit open debt.

## 1. Souriau operatorial log potential: normalized trace readout

Owner:
- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`

Isolated proof-engineer file:
- `tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialTraceClass.lean`

Mathematical context:
- `Param` is a parameter space.
- `Op` is an operator carrier with real scalar multiplication.
- `E.untracedExponential β` is the unnormalized operatorial exponential.
- `E.traceReadout` is a scalar trace/readout functional.
- `E.partitionFunction β` is defined by
  `E.partitionFunction β = E.traceReadout (E.untracedExponential β)`.
- `E.normalizedState β = (E.partitionFunction β)⁻¹ • E.untracedExponential β`.
- `E.traceReadout` is homogeneous for real scalar multiplication.
- `E.partitionFunction β ≠ 0`.

Proved proposition:
```lean
E.traceReadout (E.normalizedState β) = 1
```

Proof route:
1. rewrite by the normalized-state hypothesis;
2. use real scalar homogeneity of `traceReadout`;
3. rewrite the readout of the unnormalized exponential by the partition-function field;
4. close with `inv_mul_cancel₀`.

Live owner change:
- Replaced `traceClassClaim ... := sorry` with the native proof.
- Applied the previously isolated compile repair for two trivial `Unit` instance proofs:
  - `instSouriauNegativeLogRNDerivative.entropy_eq_Phi_add_pairing_Q_beta`
  - `instMomentMapGeneratingPotential.dPhi_eq_negative_pairing_Q`

Verification:
- `lake env lean tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialTraceClass.lean` succeeded.
- forbidden-placeholder scan on the isolated proof file returned no matches.
- At that point, `lake env lean lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean` succeeded.

Remaining open debt:
- The owner still contains explicit `sorry` warnings and impossible/overclaimed `...Claim : False := sorry` sockets.
- This pass proves only the finite algebraic normalized-trace readout; it is not analytic trace-class closure, convergence, or von Neumann algebra theory.

Next QMS candidates in the same owner:
- `duhamelFormulaClaim`: can become a theorem only if `DuhamelOperatorDerivative` stores the law as a field, or if the statement is weakened to a definitional readback.
- `firstMomentLawClaim`: can become a theorem only after adding an explicit first-moment law field or a concrete operator/trace model.
- `bkmCovarianceSymmetryClaim` and `bkmCovariancePSDClaim`: require explicit symmetry/PSD hypotheses or a genuine BKM inner-product construction.
- every `Claim : False := sorry` should be deleted/replaced by a positive data/proof-obligation structure plus proven field readbacks, not proved as `False`.

## 2. Souriau operatorial log potential: first Duhamel derivative readback

Owner:
- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`

Isolated proof-engineer file:
- `tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialDuhamel.lean`

Mathematical context:
- `Param` is the parameter carrier.
- `Op` is the operator/exponential carrier.
- `Direction` is the tangent/direction carrier.
- `D.derivativeOfExp β δ` denotes the directional derivative of the untraced operatorial exponential at parameter `β` in direction `δ`.
- `D.higherSimplexOrderedForms n β directions` denotes the ordered Duhamel/Kubo `n`-simplex operator form.
- The analytic Duhamel formula normally requires differentiability, operator topology, functional calculus, and integral/ordered-product hypotheses. Those are not present in this abstract owner surface.

QMS purification move:
- Added an explicit proof-obligation field to `DuhamelOperatorDerivative`:
  ```lean
  derivativeOfExp_eq_first_ordered_form :
    ∀ β δ, derivativeOfExp β δ = higherSimplexOrderedForms 1 β [δ]
  ```
- Replaced `duhamelFormulaClaim ... := sorry` with field projection:
  ```lean
  D.derivativeOfExp_eq_first_ordered_form β δ
  ```
- Updated `instDuhamelOperatorDerivative` with the trivial `Unit` proof `rfl`.

Proved proposition:
```lean
D.derivativeOfExp β δ = D.higherSimplexOrderedForms 1 β [δ]
```

Proof status:
- This is theorem-honest as a readback from an explicit Duhamel proof obligation.
- It is not an analytic derivation of the Duhamel formula from semigroups or functional calculus.

Verification:
- `lake env lean tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialDuhamel.lean` succeeded.
- forbidden-placeholder scan on the isolated proof file returned no matches.
- A temporary light-import copy of the live owner, replacing the unused heavy import `InfoGeometry.Canonical.SouriauTomitaModularFlowBridge` with `InfoGeometry.Canonical.StandardFormCore`, succeeded with `lake env lean`.
- Direct `lake env lean lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean` is currently blocked before checking this file body by a missing imported `.olean` for `InfoGeometry.Canonical.SouriauTomitaModularFlowBridge` / `CoordinatelessSouriauKMSBridge`.
- Attempting `lake build InfoGeometry.Canonical.SouriauTomitaModularFlowBridge` or `lake build InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge` is blocked by existing unrelated build failures in `InfoGeometry.MaxEnt.Finite` and `InfoGeometry.Quantum.RealKCategory`.

Remaining open debt after this step:
- owner `sorry_count`: 27
- owner `false_sorry_count`: 20
- `higherSimplexOrderedLawClaim` and `tracedCumulantReadoutLawClaim` remain impossible `False := sorry` sockets and must be replaced by positive proof-obligation/readback surfaces, not proved as `False`.

## 3. Souriau operatorial log potential: first-order Duhamel readout sockets

Owner:
- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`

Isolated proof-engineer file:
- `tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialDuhamelReadouts.lean`

Mathematical context:
- `Param` is the parameter carrier.
- `Op` is the operator/exponential carrier.
- `Direction` is the tangent/direction carrier.
- `D.derivativeOfExp β δ` is the directional derivative of the untraced operatorial exponential at `β` in direction `δ`.
- `D.higherSimplexOrderedForms 1 β [δ]` is the first ordered Duhamel/Kubo insertion form.
- `D.traceStateKMSReadout : Op → ℝ` is a scalar trace/state/KMS readout.
- The only available mathematical law in the owner is the first Duhamel proof obligation:
  ```lean
  D.derivativeOfExp_eq_first_ordered_form β δ
  ```

QMS purification move:
- Replaced two impossible theorem sockets with positive first-order readback theorems.
- `higherSimplexOrderedLawClaim` now states the symmetric first-order Duhamel equality:
  ```lean
  D.higherSimplexOrderedForms 1 β [δ] = D.derivativeOfExp β δ
  ```
- `tracedCumulantReadoutLawClaim` now states that scalar trace/state/KMS readout preserves the first Duhamel equality:
  ```lean
  D.traceStateKMSReadout (D.derivativeOfExp β δ) =
    D.traceStateKMSReadout (D.higherSimplexOrderedForms 1 β [δ])
  ```

Proof route:
- `higherSimplexOrderedLawClaim` closes by symmetry of `D.derivativeOfExp_eq_first_ordered_form β δ`.
- `tracedCumulantReadoutLawClaim` closes by `congrArg D.traceStateKMSReadout` applied to that first-Duhamel equality.

Proof status:
- These are genuine kernel-checked first-order readback theorems.
- They are not full higher-simplex, cumulant, trace-class, or analytic Kubo/Duhamel closure.

Verification:
- `lake env lean tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialDuhamelReadouts.lean` succeeded.
- forbidden-placeholder scan over all QMS isolated Lean files returned no matches.
- A temporary light-import copy of the live owner succeeded with `lake env lean`.

Remaining open debt after this step:
- owner `sorry_count`: 25
- owner `false_sorry_count`: 18
- next nearby targets are `firstMomentLawClaim`, `bkmCovarianceSymmetryClaim`, `bkmCovariancePSDClaim`, and `higherCumulantBoundaryLawClaim`.

## 4. Souriau operatorial log potential: moment/BKM readout block

Owner:
- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`

Isolated proof-engineer file:
- `tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialMomentReadout.lean`

Mathematical context:
- `Param` is the parameter carrier.
- `Op` is the operator/observable carrier with multiplication.
- `OperatorialExponentialFamily Param Op` supplies `normalizedState` and scalar `traceReadout`.
- `MomentGeneratingReadout.firstMoment β O` is the traced first moment of observable `O` in the normalized state at `β`.
- `MomentGeneratingReadout.bkmCovariance β A B` is a symmetric positive-semidefinite BKM covariance readout.
- `MomentGeneratingReadout.nResponseForm n β args` packages first and second response/cumulant readouts.

Existing mathlib/literature context:
- Mathlib supplies the algebra/order language used by the readbacks.
- The abstract owner does not yet construct a concrete Hilbert-space trace, Kubo--Mori integral, or BKM inner product.
- In the operator-algebra literature, the first-moment and BKM covariance laws require state/readout and positivity/symmetry hypotheses. Those cannot be derived from arbitrary functions.

QMS purification move:
- Added `[Mul Op]` to `MomentGeneratingReadout`, because the first-moment readout law contains `normalizedState β * O`.
- Added four proof-obligation fields:
  ```lean
  firstMoment_eq_trace_normalized_mul :
    ∀ β O, firstMoment β O = family.traceReadout (family.normalizedState β * O)
  bkmCovariance_symm :
    ∀ β A B, bkmCovariance β A B = bkmCovariance β B A
  bkmCovariance_self_nonneg :
    ∀ β A, 0 ≤ bkmCovariance β A A
  nResponseForm_one_two_eq :
    ∀ β A B,
      nResponseForm 1 β [A] = firstMoment β A ∧
      nResponseForm 2 β [A, B] = bkmCovariance β A B
  ```
- Replaced these four `sorry` bodies by field projections:
  - `firstMomentLawClaim`
  - `bkmCovarianceSymmetryClaim`
  - `bkmCovariancePSDClaim`
  - `higherCumulantBoundaryLawClaim`
- Repaired `instMomentGeneratingReadout` so its concrete `Unit` witness satisfies the new laws:
  - `firstMoment _ _ := 1`, matching `instOperatorialExponentialFamily.traceReadout`;
  - `nResponseForm 1 _ _ := 1`, other response orders `0`;
  - covariance readout remains zero and hence PSD.

Proof status:
- These are theorem-honest field readbacks from explicit moment/BKM proof obligations.
- They are not a native analytic construction of BKM covariance or Kubo--Mori positivity.

Verification:
- `lake env lean tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialMomentReadout.lean` succeeded.
- forbidden-placeholder scan over all QMS isolated Lean files returned no matches.
- A temporary light-import copy of the live owner succeeded with `lake env lean`.

Remaining open debt after this step:
- owner `sorry_count`: 21
- owner `false_sorry_count`: 18
- next candidates are the remaining `False := sorry` sockets beginning with `supportHypothesesClaim`, `quantumTraceClassClaim`, and `traceStateKMSReadoutRequiredClaim`.

## 5. Souriau operatorial log potential: KL/Bregman support readback

Owner:
- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`

Isolated proof-engineer file:
- `tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialBregmanSupport.lean`

Mathematical context:
- `MomentMapGeneratingPotential` carries the scalar partition potential `Φ(β)` and first variation `dΦ`.
- `SouriauKLBregmanWitness` carries `alphaPartitionPotential` as `Φ(α)`, `generator.souriau.partitionPotential` as `Φ(β)`, and `generator.dPhi alphaMinusBeta` as the linear first-variation term.
- The local algebraic Souriau/KL-as-Bregman value is
  ```lean
  Φ(α) - Φ(β) - dΦ(α-β)
  ```
  represented in the owner by `B.klValue`.

Existing mathlib/literature context:
- Mathlib supplies the arithmetic/equality language over `ℝ` used by the readback.
- In Souriau/Bregman thermodynamics, identifying KL with a Bregman divergence requires support/regularity/absolute-continuity hypotheses and convexity context.
- Those analytic hypotheses are not constructed in this owner; the owner only defines the algebraic Bregman value.

QMS purification move:
- Removed the impossible theorem surface:
  ```lean
  supportHypothesesClaim ... : False := sorry
  ```
- Reintroduced `supportHypothesesClaim` as a positive top-level readback after `klValue` is defined:
  ```lean
  theorem supportHypothesesClaim (B : SouriauKLBregmanWitness ...) :
    B.klValue = B.alphaPartitionPotential -
      B.generator.souriau.partitionPotential -
      B.generator.dPhi B.alphaMinusBeta :=
    B.KL_eq_souriau_Bregman
  ```

Proof status:
- This is a kernel-checked algebraic Bregman readback.
- It is not a proof of support regularity, convexity, absolute continuity, KL nonnegativity, or analytic Bregman divergence theory.

Verification:
- `lake env lean tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialBregmanSupport.lean` succeeded.
- forbidden-placeholder scan over all QMS isolated Lean files returned no matches.
- A temporary light-import copy of the live owner succeeded with `lake env lean`.

Remaining open debt after this step:
- owner `sorry_count`: 20
- owner `false_sorry_count`: 17
- next local sockets are `quantumTraceClassClaim` and `traceStateKMSReadoutRequiredClaim` in `QuantumOperatorialSouriauFamily`.

## 6. Souriau operatorial log potential: quantum operatorial readbacks

Owner:
- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`

Isolated proof-engineer file:
- `tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialQuantumReadout.lean`

Mathematical context:
- `LieAlgebra` is the parameter / Lie algebra carrier.
- `Obs` is an abstract operator/observable carrier.
- `Jhat β` is the quantum moment observable at parameter `β`.
- `Khat_beta` is the operatorial Souriau Hamiltonian source.
- `untracedExponential` is the unnormalized exponential operator.
- `partitionFunction` is the scalar partition function `Zβ`.
- `partitionPotential` is the scalar Massieu/log-partition potential `Φβ`.
- `rho_beta` is the normalized operatorial state proxy.
- `modularHamiltonian` is the source plus scalar log-partition correction.

Existing mathlib/literature context:
- Mathlib supplies equality and real positivity over `ℝ`.
- In operator-algebra/Souriau/KMS theory, trace-class and KMS state readouts require concrete operator topology, trace/state, positivity, and domain data.
- This abstract owner surface does not define a trace-class predicate, trace functional, von Neumann algebra, or KMS state. Therefore those analytic claims cannot be proved natively here.

QMS purification move:
- Replaced the two impossible analytic sockets:
  ```lean
  quantumTraceClassClaim ... : False := ...
  traceStateKMSReadoutRequiredClaim ... : False := ...
  ```
  with positive readbacks from existing fields:
  ```lean
  theorem quantumTraceClassClaim (Q : QuantumOperatorialSouriauFamily ...) :
    0 < Q.partitionFunction :=
    Q.partitionFunction_pos

  theorem traceStateKMSReadoutRequiredClaim (Q : QuantumOperatorialSouriauFamily ...) :
    Q.rho_beta = Q.opScale (Q.partitionFunction⁻¹) Q.untracedExponential :=
    Q.rho_beta_eq_normalized_exp
  ```

Proof status:
- These are kernel-checked readbacks of partition positivity and normalized-state construction.
- They are not proofs of analytic trace-class membership, existence of a KMS state, or a concrete trace/state readout.

Verification:
- `lake env lean tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialQuantumReadout.lean` succeeded.
- forbidden-placeholder scan over all QMS isolated Lean files returned no matches.
- A temporary light-import copy of the live owner succeeded with `lake env lean`.

Remaining open debt after this step:
- owner `sorry_count`: 18
- owner `false_sorry_count`: 15
- next local sockets are the `RenyiMellinSouriauReadout` block: `finiteSupportVolumeClaim`, `entropyDerivativeAtOneClaim`, and `petz_sandwiched_separatedClaim`.

## 7. Souriau operatorial log potential: Rényi/Mellin readouts

Owner:
- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`

Isolated proof-engineer file:
- `tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialRenyiReadout.lean`

Mathematical context:
- `State` is the state carrier.
- `gamma : ℝ` is the Rényi deformation parameter.
- `souriauPartitionAtGammaBeta` and `souriauPartitionAtBeta` are scalar partition readouts with strict-positivity fields.
- `massieuAtGammaBeta` and `massieuAtBeta` are log-partition/Massieu readouts.
- `petzRelativeRenyi` and `sandwichedRelativeRenyi` are two separate scalar Rényi readouts.

Existing mathlib/literature context:
- Mathlib supplies real arithmetic, positivity, pairs, and nonzero denominator reasoning over `ℝ`.
- In Rényi/Petz/sandwiched theory, finite support, differentiability at `γ = 1`, and comparison/separation of Petz and sandwiched divergences require support, density/operator, commutativity, and differentiability hypotheses absent from this abstract owner surface.

QMS purification move:
- Replaced three impossible analytic sockets with positive readbacks from existing fields:
  ```lean
  theorem finiteSupportVolumeClaim (R : RenyiMellinSouriauReadout ...) :
    0 < R.souriauPartitionAtGammaBeta ∧ 0 < R.souriauPartitionAtBeta :=
    ⟨R.souriauPartitionAtGammaBeta_pos, R.souriauPartitionAtBeta_pos⟩

  theorem entropyDerivativeAtOneClaim (R : RenyiMellinSouriauReadout ...) :
    1 - R.gamma ≠ 0 := by
    intro h
    apply R.gamma_ne_one
    linarith

  theorem petz_sandwiched_separatedClaim (R : RenyiMellinSouriauReadout ...) :
    (R.petzRelativeRenyi, R.sandwichedRelativeRenyi).1 = R.petzRelativeRenyi ∧
      (R.petzRelativeRenyi, R.sandwichedRelativeRenyi).2 = R.sandwichedRelativeRenyi := by
    constructor <;> rfl
  ```

Proof status:
- These are kernel-checked readbacks of partition positivity, denominator nonzero away from `γ = 1`, and ordered-pair separation of Petz/sandwiched scalar readouts.
- They are not proofs of finite support, differentiability at `γ = 1`, Petz/sandwiched comparison inequalities, or analytic continuation.

Verification:
- `lake env lean tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialRenyiReadout.lean` succeeded.
- forbidden-placeholder scan over all QMS isolated Lean files returned no matches.
- A temporary light-import copy of the live owner succeeded with `lake env lean`.

Remaining open debt after this step:
- owner `sorry_count`: 15
- owner `false_sorry_count`: 12
- next local sockets are `partitionPotentialAffineCorrectionClaim`, `onsagerPositiveSemidefiniteClaim`, optimal transport/JKO claims, and GENERIC compatibility claims.

## 8. Souriau operatorial log potential: affine cocycle readback

Owner:
- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`

Isolated proof-engineer file:
- `tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialAffineCocycle.lean`

Mathematical context:
- `State` is the state carrier.
- `LieGroup` is an abstract group/action carrier with multiplication.
- `LieAlgebra` is the parameter carrier.
- `LieDual` is the moment-map/cocycle carrier with addition.
- `LieCovarianceAndCocycle` supplies a Souriau moment map, state action, coadjoint action, beta action, affine cocycle, strict equivariance, and the cocycle law.

Existing mathlib/literature context:
- Mathlib supplies equality and the algebraic operations `[Mul LieGroup]` and `[Add LieDual]` used by the cocycle identity.
- In Souriau affine coadjoint thermodynamics, partition-potential affine corrections require transformed-potential/readout fields not present in this owner surface.

QMS purification move:
- Replaced the impossible partition-potential analytic socket with the explicit affine cocycle law already carried by the structure:
  ```lean
  theorem partitionPotentialAffineCorrectionClaim
      (L : LieCovarianceAndCocycle ...) (g h : LieGroup) :
      L.cocycle (g * h) = L.coadjointAction g (L.cocycle h) + L.cocycle g :=
    L.affineCocycle g h
  ```

Proof status:
- This is a kernel-checked affine cocycle readback.
- It is not a theorem about partition-potential transformation under affine coadjoint action.

Verification:
- `lake env lean tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialAffineCocycle.lean` succeeded.
- forbidden-placeholder scan over all QMS isolated Lean files returned no matches.
- A temporary light-import copy of the live owner succeeded with `lake env lean`.

Remaining open debt after this step:
- owner `sorry_count`: 14
- owner `false_sorry_count`: 11
- next local socket is `onsagerPositiveSemidefiniteClaim`, followed by the optimal transport/JKO and GENERIC compatibility sockets.

## 9. Souriau operatorial log potential: Onsager dissipativity readback

Owner:
- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`

Isolated proof-engineer file:
- `tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialOnsager.lean`

Mathematical context:
- `State` is the state carrier.
- `Observable` is the abstract observable carrier.
- `Density State` is represented as a scalar density/readout function `State → ℝ`.
- `SouriauMetriplecticOnsager` carries a reversible flow, relative free energy, variational force, Onsager operator, and scalar free-energy derivative.
- The structure explicitly supplies `freeEnergyDerivative_nonpos : ∀ ρ, freeEnergyDerivative ρ ≤ 0`.

Existing mathlib/literature context:
- Mathlib supplies the order relation on `ℝ` and direct theorem projection.
- In Onsager/metriplectic theory, positive-semidefiniteness of an Onsager tensor is a bilinear/quadratic-form property requiring symmetry and positivity hypotheses absent from this owner surface.

QMS purification move:
- The live owner theorem is the scalar dissipativity readback:
  ```lean
  theorem onsagerPositiveSemidefiniteClaim
      (O : SouriauMetriplecticOnsager State Observable) (ρ : Density State) :
      O.freeEnergyDerivative ρ ≤ 0 :=
    O.freeEnergyDerivative_nonpos ρ
  ```
- The isolated proof-engineer file proves the same theorem body by field projection.

Proof status:
- This is a kernel-checked scalar free-energy dissipativity theorem.
- It is not tensor-level Onsager positive semidefiniteness.

Verification:
- `lake env lean tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialOnsager.lean` succeeded.
- forbidden-placeholder scan over the isolated Onsager file returned no matches.
- A temporary light-import copy of the live owner succeeded with `lake env lean`.

Auxiliary compile repair:
- The downstream `OptimalTransportWitness.freeEnergy_jko_decrease` field had an untyped unused binder:
  ```lean
  ∀ x, freeEnergy (fun _ => 1) ≤ freeEnergy (fun _ => 1)
  ```
- Lean could not infer the binder type, causing the owner body check to fail before downstream declarations.
- It was repaired narrowly to:
  ```lean
  ∀ x : State, freeEnergy (fun _ => 1) ≤ freeEnergy (fun _ => 1)
  ```

Remaining open debt after this step:
- owner `false_sorry_count`: 0
- at this intermediate checkpoint, residual readback surfaces still needed a consolidated isolated QMS audit; see §10 for the completed audit and final placeholder count.

## 10. Souriau operatorial log potential: residual readback-repair audit

Owner:
- `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`

Isolated proof-audit file:
- `tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialReadbackRepairs.lean`

Mathematical context:
- `RegularizedJacobianPotential` now exposes the remaining entropy-readout requirement as an explicit proposition field carried by each concrete model, rather than an unproved analytic theorem.
- `ModularHamiltonianData` carries the two explicit Gibbs/modular readback laws:
  `densityOperator = exp (-gibbsHamiltonian - logPartitionScalar • 1)` and
  `negativeLogDensity = gibbsHamiltonian + logPartitionScalar • 1`.
- `OptimalTransportWitness` and `GenericMetriplecticCompatibility` expose their JKO/transport/GENERIC assertions as concrete readback fields.

Existing mathlib/literature context:
- Mathlib supplies the algebra/order notation used by these readbacks.
- The analytic literature behind Gibbs formulas, modular Hamiltonians, JKO schemes, and GENERIC/metriplectic compatibility requires additional hypotheses not present in this owner: concrete state spaces, exponential/trace semantics, lower semicontinuity, coercivity, compactness, Wasserstein geometry, and bracket/tensor positivity.

QMS purification move:
- The remaining live theorem names are field-readback theorems, not `False` sockets and not hidden proof holes.
- The isolated proof-audit file checks all corresponding readback patterns directly.

Verification:
- `lake env lean tools/multisystem/qms_purification/lean/SouriauOperatorialLogPotentialReadbackRepairs.lean` succeeded.
- Forbidden-placeholder scan over the isolated readback-repair file returned no matches.
- Owner scan for `False := sorry`, `theorem .*Claim.*:= sorry`, `:= sorry`, and bare `sorry` found no live proof placeholders; the sole `sorry` string is documentation text in a comment.

Final owner debt status for this slice:
- live proof-placeholder debt: 0
- live `False := sorry` debt: 0
- open analytic closure debt remains semantic, not hidden in proof holes: trace/KMS analysis, true Gibbs trace-class construction, tensor-level Onsager PSD, Wasserstein/JKO compactness/coercivity/lsc, and full GENERIC bracket compatibility.
