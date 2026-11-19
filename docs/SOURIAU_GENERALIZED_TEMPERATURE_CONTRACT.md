# Generalized Souriau temperature on the full matrix algebra

## Intake and source revision

The user asked what temperature means in Souriau thermodynamics when the
symmetry charges do not commute, how the inverse-temperature parameter becomes
an operator generator, and how this relates to heat, work, cycles, and Landauer
erasure. The subsequent instruction authorizes preparation and upstream
publication of a pull request. Publication is a draft for review, not a merge.

The motivating intake includes: “betha is not a scalr it becomes and operator
vector of operators perhaps what is it and how do we formulzte heat cycles work
landrauer principle in soureau theormodynamic and dynamcis”. The earlier cycle
intake also mentions radial Bloch motion, Weyl scaling, equilibrium leaves,
unitary motion, and reversible/irreversible evolution. These physical
interpretations are preserved as motivation; they are not additional Lean
hypotheses or conclusions.

This change starts from PR407 at
`b08a77270768370cd77f4c8861b009e179daa716`, whose base is PR399. Both were open
drafts when checked on 2026-11-19. Upstream `main` was
`fea96b564201654cd4693008585039a56f66adf3`. The new PR is stacked on PR407 to
reuse its actual CFC Gibbs, entropy, and unitary-transport proofs.

The dependency pins remain Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Formal intent and proved contracts

Scope: finite-dimensional full noncommutative complex matrices. The inverse
temperature coordinates and the charge pencil are real. No pairwise
commutation of the charges and no commutation of a comparison density with the
Gibbs generator is assumed. These are finite-stage mathematical statements;
they do not construct an infinite-dimensional modular algebra or a Lie-group
moment map.

Let `n` be a finite, nonempty index type and `Mat = Matrix n n ℂ`. For a finite
family of Hermitian charges `Q a`, construct the real-linear map

\[
K_\beta=\sum_a\beta_a Q_a.
\]

Use the existing `MatrixGibbsEntropy.normalizedGibbsDensity K hK 1`, denoted
\(\Gamma_K\), rather than defining a second density or entropy API. The
existing `matrixEntropy` is \(-\operatorname{ReTr}(\rho\log\rho)\), with the
actual `CFC.log`.

| Target | Exact hypotheses and conclusion | Discharged proof obligation |
|---|---|---|
| Charge pencil | Real linearity, Hermiticity from Hermitian charges, and distribution of the trace pairing | Native kernel check passed |
| Generalized Gibbs logarithm and entropy | Actual normalized CFC state; `log Γ = -K - log Z • 1` and `s Γ = Σ βa ⟨Qa⟩Γ + log Z` | Native finite-charge consumer of the existing matrix identities |
| Generalized bath balance | Any trace-one comparison matrix; weighted charge increase equals its entropy increase plus actual relative-log trace | Native kernel check passed without commutation |
| Generator gauge | For Hermitian `K,L`, `ΓK = ΓL` iff `K = L + c • 1` for a real `c` | Converse proved from the actual Gibbs logarithm |
| Unitary endpoint compatibility | `ΓK = U ΓL U*` iff `K = U L U* + c • 1`, for a native unitary matrix | Converse proved from scalar gauge and native unitary covariance |
| Matrix Klein inequality | Strictly positive `A,B`; `ReTr A(log A - log B) ≥ ReTr A - ReTr B` | Proved using two independent eigenbases |
| Relative entropy nonnegativity | Strictly positive, trace-one matrices; actual relative-log trace is nonnegative | Consumer of matrix Klein |
| Generalized bath entropy bound | A strictly positive, trace-one final bath state; `Σ βa Δ⟨Qa⟩ ≥ Δs` | Consumer of the exact bath balance and matrix Klein |
| Entropy maximization | Faithful trace-one comparison states with the same means for every charge have entropy at most the generalized Gibbs entropy | Consumer of the generalized bath entropy bound |
| Gibbs passivity | Native unitary conjugation of the actual Gibbs density cannot lower the expectation of its own generator | Consumer of entropy invariance and matrix Klein |
| Conserved-charge stationarity | If a distinct Hamiltonian commutes with each charge, its commutator flow annihilates the actual generalized Gibbs state | Consumer of the CFC centralizer theorem |

All targets in this table passed the native kernel and axiom checks recorded
below. The matrix Klein proof keeps the relative spectral overlap and does
not assume simultaneous diagonalization.

## Existing owners and bounded search

The source search covers the actual canonical, operator-algebra, quantum,
modular, and thermodynamic owners under `lean/` and related `src/` owners, their
imports and consumers, and the pinned Mathlib spectral/CFC API. Documentation
and historical reports are navigation only.

| Existing owner | Reused declaration or observed boundary |
|---|---|
| `Canonical/MatrixGibbsEntropy` | Actual CFC Gibbs exponential/logarithm, normalized trace-one strictly positive state, `gibbs_energy_entropy_balance` |
| `Canonical/MatrixGibbsScaleTransport` | Central shift invariance and unitary covariance of the Gibbs state |
| `Canonical/MatrixEntropyUnitaryOrbit` | Actual entropy and unitary invariance for strictly positive states |
| `Canonical/MatrixGibbsMetriplecticEquilibrium` | Stationarity under the generator's own commutator, with mobility annihilating the identity |
| `Canonical/FiniteSelfAdjointGibbsStateBridge` | Genuine noncommutative log-partition directional derivative on continuous endomorphisms |
| `Canonical/NoncommutativeGibbsBKMHessianBridge` | Actual second derivative and centered BKM form on the continuous-endomorphism carrier |
| `Canonical/GibbsHessianScalarGaugeBridge` | Generic real parameter Hessian kernel is exactly scalar charge directions; no duplicate metric is introduced |
| `Canonical/OperatorValuedSouriauFamily` | Abstract family fields do not by themselves construct the actual Gibbs exponential, logarithm, or positivity |
| `OperatorAlgebra/NoncommutativeRenyi` | Actual noncommutative relative-log kernel; no general matrix Klein theorem found in the inspected declarations |
| `Modular/QuantumDataProcessingInequality` | Its named Klein inequality is for supplied probability spectra, not two arbitrary matrix states |
| `Quantum/FinitePartialTrace` | Actual finite matrix partial trace; this alone does not prove tensor entropy additivity |

Mathlib provides the Hermitian spectral theorem, independently chosen unitary
eigenbases, Hermitian functional calculus, positive eigenvalues of positive
definite matrices, and the scalar logarithm inequality. The Klein
proof uses overlap weights `normSq (U_A* U_B)ᵢⱼ`, with row and column sums one.
It retains the full matrix relative entropy; it does not replace the matrices
by their spectra in a shared basis.

## Overlapping upstream work

PR406 at `8abcfcd8e1cb9254533fc6f6ecacf0567a1aa91d` constructs native
replacement relaxation, Gibbs stationarity, and detailed-balance/Dirichlet
identities. Its inspected owners do not supply matrix relative-entropy
nonnegativity or a joint erasure process.

PR408 at `6ffd81209115217c232cbe981c10f8119dc017e2` constructs real-matrix
Gibbs/Carnot calculus. Its smooth affine paths have actual integrated heat and
work currents, supported by noncommutative Duhamel trace differentiation. This
PR does not duplicate that scalar-temperature engine. Its contribution is the
real multicharge generator, generator gauge classification, and the proved
full-matrix entropy inequality.

## Interpretation and remaining obligations

In Souriau's formulation the generalized inverse temperature is an element of
the symmetry Lie algebra. In a finite observable representation, real
coordinates select the Hermitian `Kβ`. This change constructs that finite
charge pencil; it does not construct the Lie algebra, a symplectic moment map,
or their representation laws. An arbitrary product of an operator called
`beta` with a Hamiltonian need not be Hermitian and is not used here.

The physical energy component gives `βE = 1 / (kB T)` after the energy charge
and units are chosen. A general vector of thermodynamic multipliers has no
canonical scalar reciprocal temperature. Nonparallel bath multiplier vectors
do not yield a universal scalar Carnot ratio by taking their norms.

Stationarity for the Gibbs generator's own commutator is distinct from
stationarity for a separate physical Hamiltonian. The latter requires the
corresponding conservation/commutation statement. Positive mobility or a
decreasing free-energy readout alone does not construct a positive,
trace-preserving dynamical flow.

The exact bath identity and its proved entropy bound do not yet prove a
system erasure theorem. A full joint-unitary Landauer result still requires
the actual tensor-log identity, tensor entropy additivity, faithful marginal
construction, and identification of final mutual information with matrix
relative entropy. Those would establish

\[
\beta\cdot\Delta q_B=-\Delta s_S+I(S:B)_{\rm final}
 +D(\rho_B'\Vert\Gamma_B)\ge-\Delta s_S
\]

for an initially uncorrelated system and Gibbs bath with the stated unitary
process. No such tensor/process assumptions are hidden in a new structure.
Exact pure-state erasure, nonfaithful boundary states, an entropy-carrying
battery, initially correlated systems, infinite reservoirs, physical Weyl
geometry, and spacetime identification require separate contracts.

## Independent roles

Generation: `souriau_gibbs_owner` and `souriau_landauer_audit`, each writing
isolated candidates. Independent semantic audit: `souriau_semantic_review`.
Independent final acceptance: `souriau_native_qa`. The coordinating parent
reviews and integrates candidate files and runs preliminary checks; it does
not author the theorem proofs.

## Dependency order and theorem map

The dependency order follows actual Lean imports and proof applications:

1. The existing CFC Gibbs logarithm gives generic scalar gauge classification.
   Hermitian charges separately give `chargePencil_isHermitian`, which
   instantiates the Gibbs logarithm and entropy balance for the finite charge
   family.
2. Independently diagonalized matrices give a native unitary overlap. Its row
   and column sums and the mixed CFC trace formula give matrix Klein.
3. The exact charge balance and matrix Klein give the bath entropy bound and
   entropy maximization. Unitary entropy invariance then gives passivity.
4. Conservation of each charge gives commutation with the pencil, and the CFC
   centralizer theorem gives stationarity for the separately named Hamiltonian.

| New owner | Public mathematical entry points |
|---|---|
| `Canonical/MatrixGeneralizedGibbs.lean` | `chargePencil`, `trace_mul_chargePencil`, `gibbs_charge_entropy_balance`, `normalizedGibbsDensity_one_eq_iff`, `normalizedGibbsDensity_parameter_eq_iff`, `normalizedGibbsDensity_one_eq_unitary_iff`, `unitaryFlow_chargePencil_eq_zero` |
| `Canonical/MatrixRelativeEntropy.lean` | `unitaryOverlap`, `trace_mul_cfc_eq_overlap_sum`, `relativeLogTrace_ge_trace_sub`, `relativeLogTrace_nonneg` |
| `Canonical/MatrixGeneralizedGibbsInequalities.lean` | `entropy_change_le_charge_gain`, `matrixEntropy_le_gibbs_of_charge_eq`, `gibbsEnergy_le_unitary_energy`, `gibbs_charge_le_unitary_charge` |

These owners add 26 public theorems, five private proof lemmas, and two native
constructions. The full declaration audit below also includes generated
implementation declarations.

The `c • 1` ambiguity concerns normalization of exponential weights. Relating
it to a spacetime Weyl transformation requires an explicit geometric map.

## Observed verification

Independent A-A review passed the exact source hashes below. Independent QA-A
accepted the change as `ACCEPTED_WITH_LIMITED_SCOPE` at local source commit
`188ab2e3b76bbd9592f7a5db2ad2435db1bf52fa`, tree
`40b6c902560d6a288fa250b0257bb05653d29823`.

The fresh command, run from the independent checkout root, was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/85b0f1eb27b8/lean_verification_runtime/mathlib4 \
  --lean /workspace/scratch/85b0f1eb27b8/lean_verification_runtime/lean-4.34.1/bin/lean \
  --output /workspace/scratch/0b027a897d29/souriau-verification/final-qa \
  --target InfoGeometry.Canonical.MatrixGibbsEntropy \
  --target InfoGeometry.Canonical.MatrixGibbsScaleTransport \
  --target InfoGeometry.Canonical.MatrixUnitarySpectralOrthogonality \
  --target InfoGeometry.Canonical.MatrixGibbsMetriplecticEquilibrium \
  --target InfoGeometry.Canonical.MatrixGeneralizedGibbs \
  --target InfoGeometry.Canonical.MatrixRelativeEntropy \
  --target InfoGeometry.Canonical.MatrixGeneralizedGibbsInequalities
```

It exited zero. No incremental repository artifact reuse or omitted axiom
check was requested. All 18 repository modules in the import closure compiled
freshly. Every selected owner had zero errors and zero warnings. The 12
warnings in unchanged prerequisite owners were recorded separately.

| Selected owner | Native declarations audited |
|---|---:|
| `MatrixGibbsEntropy` | 22 |
| `MatrixGibbsScaleTransport` | 23 |
| `MatrixUnitarySpectralOrthogonality` | 18 |
| `MatrixGibbsMetriplecticEquilibrium` | 11 |
| `MatrixGeneralizedGibbs` | 22 |
| `MatrixRelativeEntropy` | 27 |
| `MatrixGeneralizedGibbsInequalities` | 7 |
| Total | 130 |

The three new owners account for 56 audited declarations. The native audit
allows only `propext`, `Classical.choice`, and `Quot.sound`, and found no other
transitive axioms. Source and helper hashes were reconciled independently
against the completed report and actual native declaration output.

All eight static commands exited zero: strict OpenGauss screening, strict
refutation, Gate 4 source preflight, warning-strict semantic-vacuity checking,
lexical debt checking, and three strict placeholder scans. Every finding count
was zero, including soft and advisory placeholder findings. Gate 4 alone
reports `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`; the separate native run above
supplies the kernel evidence.

The workflow YAML and all three embedded Python blocks parsed, and its exact
seven target names and path filters were checked. The four maintained build,
source-closure, and axiom-audit helpers are unchanged from the base.

The installed pre-commit hook ran on the six-file source change and reported
`proof_proxy_staged_gate: ok`. The actual new-branch pre-push hook is recorded
separately below; no scoped result is a root-package build certificate.

### Source fingerprints

| New owner | SHA256 |
|---|---|
| `MatrixGeneralizedGibbs.lean` | `2c8b66cf9607bdc3bb3df717c1cbf743e99ca7f1783129e90d66e1dd969d32b0` |
| `MatrixRelativeEntropy.lean` | `3ddf7572b912e1d925de7ef9209fedbfac534bea2c450f3f5b4bfcfc8323627a` |
| `MatrixGeneralizedGibbsInequalities.lean` | `102e376b99b49c88bc262acaed8ccb7c5052b7e89323fc452255b1de02ca825e` |

The scoped workflow SHA256 is
`a0c78e406a1c326c2f37853ffdd07329cf4f5d09295afdfca7aae5bf96ade6f4`.
The independent `qa-acceptance.json` SHA256 is
`de5d10966807a48c4c307bf064a726f1ec6aebfe15d59cacd957114d06650645`.
The QA evidence manifest hashes 57 evidence files. These local report
fingerprints identify the observed run; the upstream workflow independently
uploads its own exact-head reports and source snapshots.

### Root integration and publication

The actual installed new-branch pre-push hook ran on the verified source commit
`188ab2e3b76bbd9592f7a5db2ad2435db1bf52fa`, with the zero remote object ID and
`origin/main` ancestry. It exited 1. Its locked root Lake build stopped during
dependency resolution because
`external_refs/homotopy-hypothesis-lean4` is absent. This is a failed root
publication gate, not a successful whole-repository build.

The hook's remaining checks completed: the eight changed Lean files in the
stacked range had zero lexical proof gaps; the semantic content scan selected
27,282 files with zero blocking findings; the tracked-source scope and
quarantined-artifact checks passed. These static results do not replace the
failed root build.

A separate path preflight found `external_refs/atlas-lean` also absent and the
pinned GIFT gitlink uninitialized. The HomotopyHypothesis and Atlas path entries
in `lake-manifest.json` do not contain reconstructible git revisions. No
replacement packages, stub proofs, dependency pin changes, cache deletion, or
weakened verification helpers were introduced.

The pre-push log SHA256 is
`8a4efb7c45ec0e3cf68dc761981067e543fa220df0b4e1a4dd0bbaedb966434d`;
its command/result JSON SHA256 is
`6c0b30864b79d469605c561d73418da2baa0f978861c29c50c3caa542030ae2e`.

At the user's explicit request, the verified source is published as a draft
for upstream review, with root integration still blocked. No merge or
whole-repository acceptance is claimed.

The final documentation update changes no Lean source, workflow, dependency
pin, or verification helper relative to the checked source commit. The pull
request body records the published Git tree and its exact relation to this
local verification source. The published PR remains a draft stacked on PR407.

## Literature context

- Charles-Michel Marle, [On Gibbs states of mechanical systems with symmetries](https://marle.perso.math.cnrs.fr/pdffiles/2020/GibbsStatesJGSPPart1.pdf), 2020: the Lie-algebra parameter and moment-map formulation motivating the real charge pencil.
- Yelena Guryanova and coauthors, [Thermodynamics of quantum systems with multiple conserved quantities](https://arxiv.org/abs/1512.01190), 2016: noncommuting conserved charges and constraints on their weighted exchange.
- David Reeb and Michael M. Wolf, [An improved Landauer principle with finite-size corrections](https://arxiv.org/abs/1306.4352), 2014: the joint-process equality and its correlation/relative-entropy terms, recorded here as a boundary for the bath-only result.

These sources motivate the contracts; the Lean declarations and their kernel
checks determine the mathematical scope actually delivered.
