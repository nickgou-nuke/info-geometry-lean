# Craig lattice chiral fermion intake: bounded owner search

**Superseding result:** PR #395 appeared after the snapshot below. The current draft reuses its Ginsparg-Wilson owner and retains only the native matrix spectral-sign construction and its integration. See the final section for exact revisions and maps.

## Scope and status

This is a source reconnaissance and candidate contract, not a Lean acceptance report.
The repository is `nickgou-nuke/info-geometry-lean`. Remote main was read at
`08c34e03f610b452e03422037949196dc7d92d6d`; the local read-only checkout was
`fa8689f792024c621086a0305582269242f1d23b`. A targeted Git diff confirmed that the
principal Peirce, Kato, realification, algebraic Berry-curvature, and energy-sign
owners below are unchanged between those revisions.

The current open-PR metadata was refreshed at **2026-11-17 13:54:55 UTC**:
37 open PRs, #357 through #393. Every open PR's changed-file inventory was
retrieved. The refreshed inventories for the three heads that moved during
reconnaissance (#375, #381, #385) were read again. This is an inventory-level
de-duplication across all open PRs, supplemented by actual source inspection of
relevant owners; it is not a full proof review of every PR.

Searches covered canonical `lean/InfoGeometry` source, related imports and
consumers, and the matching `src/` and `proofs/` source surfaces through Git
objects where omitted from the checkout. Search families included Kato,
projector tangency/comparison/transport, Peirce odd products, cyclic trace,
Berry curvature, Chern–Weil/transgression, determinant line/phase, overlap
Dirac, Ginsparg–Wilson, Neuberger, Lüscher, Craig, and the arXiv identifier.
No named Ginsparg–Wilson or native spectral-sign construction was found in
that bounded search. Open PR titles and bodies had no matches for
`2610.09093`, `Nathaniel Craig`, `fermion measure`, `Kato`, `Lüscher`,
or `Ginsparg`.

No compiler, Lake build, cache action, commit, or publication was performed by
this subtask. The isolated Lean source remains a candidate until the parent
runs the maintained checks and independent review.

## Paper boundary

The intake is Nathaniel Craig, *A gauge-invariant measure for lattice chiral
fermions*, [arXiv:2610.09093v1](https://arxiv.org/abs/2610.09093v1).
The supplied PDF has 126 pages. Printed page 11 (PDF page 14), equations
(2.6)–(2.9), defines
`D = 1 + Γ sign(H)`, states the Ginsparg–Wilson relation, and uses
`Γhat = Γ(1-D) = -sign(H)`, hence `P̂₋ = (1+sign(H))/2`.
The gap of H does not imply invertibility of D.

Section 5 starts at printed page 22 (PDF page 25). Its finite comparison lemma
assumes one fixed finite-dimensional complex Hilbert space and a smooth gapped
Hermitian family. It asserts curvature transgression and determinant-phase
comparison for every closed curve. Its algebraic engine is tangency of
projector derivatives, odd-product routing, and cyclic trace cancellation.
Those algebraic ingredients already have repository owners.

The primary paper links the author's mathematical companion and Lean
formalization at [DOI 10.5281/zenodo.23196062](https://doi.org/10.5281/zenodo.23196062)
and an [official Lean verification report](https://arxiv.org/src/2610.09093v1/anc/lean-verification-report.pdf).
The coordinator inspected that report. This subtask has not obtained or
audited the archive's Lean source and does not claim that the paper's
transgression or global measure theorem is absent from the author's work.
The new candidate is an integration into this repository's pinned native
Mathlib matrix carrier, not a reproof or validation of the full paper.

## Existing native owners and precise reuse

All repository source links in this section are pinned to the observed main
commit. A theorem name below identifies its owner namespace unless noted.

| Owner | Exact reusable declarations and scope | Inspected consumers / boundary |
|---|---|---|
| [Core/PeirceGrading.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Core/PeirceGrading.lean) | `even`, `odd` are native integer-linear endomorphisms of an arbitrary associative ring. `odd_apply` is the sum of the two directed off-diagonal corners. `mem_odd_iff hp` is exactly `x ∈ range(odd p) ↔ p*x+x*p=x`. `odd_mul_odd`, `even_mul_odd`, and `odd_mul_even` route ordered products. | Consumed by Peirce QGT, Peirce coupling, Peirce curvature, and NCG owners. Three tangent factors are odd by composing existing multiplication rules; this alone supplies no derivative or differential form. |
| [Canonical/IdempotentOrbitContracts.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Canonical/IdempotentOrbitContracts.lean) | For `p*p=p` and `p*v+v*p=v`, `tangent_diagonal_zero` proves `p*v*p=0`; `tangent_split` gives the two-corner decomposition; `tangent_horizontal_lift` proves `[[v,p],p]=v`. `generator_ambiguity` identifies equal inner derivatives with a centralizer difference. | `Canonical.IntegralCyclotomicTransvection`, `Canonical.FiveStreamNativeTransport`, audit and aggregator. This is the compact Kato-generator algebra owner. It does not solve a path ODE. |
| [OperatorAlgebra/NoncommutativeGradedTrace.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/OperatorAlgebra/NoncommutativeGradedTrace.lean) | `IsCyclic τ` is cyclicity of an additive functional on an arbitrary ring. `cyclicFunctional_directedCorners_eq_zero` kills each off-diagonal corner separately, with no 2-torsion assumption. `gradedTrace_oddCorner_eq_zero` applies when the weighting operator commutes with p. | `NoncommutativeConnesCalculus`, `NoncommutativeKrausChannel`, and chiral index/supertrace owners. Together with Peirce routing this already yields the triple-tangent trace cancellation used in Section 5. |
| [OperatorAlgebra/PeirceQuantumGeometricTensor.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/OperatorAlgebra/PeirceQuantumGeometricTensor.lean) | `peirceTangent_mem_odd`, `tangent_product_mem_even`, `tangent_product_commutes`, `cyclicFunctional_peirce_diagonal_split`, `cyclicFunctional_tangent_curvature_core_complement_cancel`, and matrix `tangent_curvature_core_complement_trace_cancel`. Ordered full operators are retained. | `YangMillsOrbitGramian`, `NoncommutativeConnesCalculus`, aggregators. Corner cancellation does not make the core Berry curvature vanish. |
| [Clifford/ChiralProjectorBerryCurvature.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Clifford/ChiralProjectorBerryCurvature.lean) | `projectorCurvature P A B = P*(A*B-B*A)*P`; `projectorCurvature_swap`. Relative-curvature and twist-defect theorems are equivalences/readbacks from an explicitly supplied transport equality. | `OperatorAlgebra.PeirceCompressionCurvature`. No parameter derivative, curvature closedness, or interval transgression is constructed here. |
| [Quantum/Realification.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Quantum/Realification.lean) | Arbitrary finite rectangular `realify`; `realify_mul`, `realify_conjTranspose`, `realify_star`, `realify_injective`, `trace_realify`; `internalJ`, `internalJ_eq_realify`, `internalJ_sq`; `realify_commutes_internalJ`, `realify_unrealify_of_commute`, and `mem_range_realify_iff_commute`. | States, channels, tensors, compression, and category owners. The whole complex matrix algebra is represented faithfully in the real J-commutant; factors are never forced to commute with each other. |
| [Quantum/RealificationCategory.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Quantum/RealificationCategory.lean) | `doubledRealK`, `realifiedHom`, `realify_intertwines_internalJ`, `coordinateIso`, `coordinateIso_naturality` connect matrix realification to the existing `RealKVect` category. | This is an actual carrier map and naturality theorem; it should be reused if a later result claims categorical compatibility. |
| [OperatorAlgebra/EnergySignInvolution.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/OperatorAlgebra/EnergySignInvolution.lean) | `EnergySign.energySignInvolution H E hE hH` constructs H/E from the special relation `H*H = E^2 • 1`. It proves an involution and explicit inverse. | Consumed by `Physics.DiracEnergyOddPart`. This does not construct spectral sign for a general invertible Hermitian H with several distinct eigenvalue magnitudes. |
| [OperatorAlgebra/ChiralProjectorFromInvolution.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/OperatorAlgebra/ChiralProjectorFromInvolution.lean) | `ChiralInvolution` with `chi_sq`; derived `Pleft`, `Pright`, their idempotence, annihilation, sum, difference, and eigenvalue laws. | Broad existing chiral layer, including `CliffordWeyl.ChiralIdeals`. Do not create another general projector packet merely to repeat these laws. |

Two further Kato-named sources were read:
[Canonical/VietaIKKTLaxBerryDarkMatterTemperleyLiebHodgePoset.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Canonical/VietaIKKTLaxBerryDarkMatterTemperleyLiebHodgePoset.lean),
`Gamma_Kato` and `kato_adiabatic_berry_transport), and
[OperatorAlgebra/PeirceSpine/VietaSusyKatoDissipationAndGaloisGolayPoset.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/OperatorAlgebra/PeirceSpine/VietaSusyKatoDissipationAndGaloisGolayPoset.lean),
`kato_berry_spectral_flow_and_covariant_time`.
Their actual results are finite ring identities under the differentiated
idempotency equation. Their names/docstrings do not establish an ODE solution,
unitary path transport, or determinant holonomy. The compact
`IdempotentOrbitContracts` API is preferable for the same algebra.

## Nearby names whose types do not close Section 5

- [Canonical/ChernSimonsTransgressionKernel.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Canonical/ChernSimonsTransgressionKernel.lean)
  proves an actual degree-three to degree-four exterior-algebra identity
  `d Tr(A dA + (2/3)A³) = Tr((dA+A²)²)` for a supplied square-zero graded
  derivation and homogeneous forms. It is not the projector-family
  degree-one to degree-two transgression, interval FTC, or cylinder holonomy.
- [Optics/OperatorValuedConnection.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Optics/OperatorValuedConnection.lean)
  supplies an explicit derivative channel. Its structure does not require
  that channel to be a native Fréchet derivative.
- [Optics/LocalGaugeCovariantDerivative.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Optics/LocalGaugeCovariantDerivative.lean)
  defines `SatisfiesAdjointBianchi` by vanishing of every directional adjoint
  derivative for two fixed curvature slots. This is a strong supplied
  directional condition, not automatically the cyclic exterior Bianchi
  identity. `OperatorQGTChernWeil` consumes that condition.
- [Canonical/DeterminantPhaseVolumeBridge.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Canonical/DeterminantPhaseVolumeBridge.lean)
  has an arbitrary `detReadout`; its flow-invariance result reads a supplied
  `FlowPreservesDeterminant` hypothesis.
- [Volume/DeterminantBundle.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Volume/DeterminantBundle.lean)
  defines `DeterminantLine V := ℝ`, with positive absolute determinant
  scaling. It is not the paper's complex top-exterior-power determinant line
  or its phase connection.
- [Physics/ChiralProjectorTransport.lean](https://github.com/nickgou-nuke/info-geometry-lean/blob/08c34e03f610b452e03422037949196dc7d92d6d/lean/InfoGeometry/Physics/ChiralProjectorTransport.lean)
  proves finite real matrix half-projector transport from a supplied
  intertwining equation. It does not construct a moving projector path.

## Real phase convention

For the existing standard realification R and J = R(i·1),

`Tr_R(J * R(X)) = -2 Im(Tr_C X)`.

Consequently, when `Tr_C(P[A,B])` is purely imaginary (Hermitian P,A,B),

`i Tr_C(P[A,B]) = ofReal (½ Tr_R(J * R(P[A,B])))`.

The factor is +1/2 with the repository's J convention. Ordinary unweighted
real trace loses this phase. This identity is a possible later repository
bridge; it is not part of the present spectral-sign candidate and no new
theorem is claimed for it here.

## Open-PR overlap at the inspected scope

The full inventory of 37 changed-file lists contains no new owner named or
positioned as native matrix spectral sign, Ginsparg–Wilson/overlap Dirac,
projector-family transgression, or Lüscher reconstruction.

Relevant neighboring work remains reusable and separate:

- #362: partial-isometry/groupoid and `PeirceRoundTripCounterexamples`.
  The latter was read at its exact head: its native spectra concern nonzero
  square-zero corner products, not Hermitian spectral sign.
- #372 and #379: `InternalPhaseGram`, `PhaseLinearObservableCommutator`,
  `PhaseObservableUncertainty`, and native Hestenes right-phase extensions.
  These concern positive pairings, centered commutators, and uncertainty.
- #375 and #376: real internal-phase Fourier/Gram and projective QGT matrix
  owners. Their changed-file lists were inspected.
- #377: `RealKreinTrace` was read at its exact head. Its parity and
  transpose/Krein weighted trace identities do not construct phase-weighted
  projector curvature or a spectral sign.
- #378: exchanged projection pairing and real loxodromic flows.
- #380 and #381: real spacetime and native Hestenes spectral corners, with
  adjoint/reversion distinctions. These are algebraic corners of existing
  involutions; no general matrix spectral-sign construction appears in their
  inspected changed-file inventories.
- #385 and #391: native Dirac current/continuity and their counterexample
  boundaries, not the finite overlap Dirac construction.

Only source or inventories explicitly described above were inspected.
A differently named declaration elsewhere in an unreviewed PR body is not
ruled out by filename inventory alone.

## Pinned Mathlib APIs used by the candidate

All Mathlib links are pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612` (repository Lean 4.34.1).

| Source | Exact API and role |
|---|---|
| [Analysis/Matrix/HermitianFunctionalCalculus.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean) | `Matrix.IsHermitian.instContinuousFunctionalCalculus` gives real functional calculus on matrices over any RCLike field. `Matrix.IsHermitian.cfc_eq` identifies it with native spectral evaluation. No external diagonalizing witness is an API assumption. |
| [Analysis/Matrix/Spectrum.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Matrix/Spectrum.lean) | `Matrix.finite_real_spectrum`, native Hermitian eigenvalues and spectral theorem. |
| [Topology/Separation/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Topology/Separation/Basic.lean) | `Set.Finite.continuousOn` makes Real.sign continuous on each finite matrix spectrum; no global continuity of Real.sign is asserted. |
| [Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean) | `cfc`, `cfc_predicate`, `cfc_mul`, `cfc_congr`, `cfc_const_one`, `isUnit_cfc_iff`, `cfc_pow_id`, `eqOn_of_cfc_eq_cfc`, `cfc_id'`. Actual signatures and relevant proof bodies were read. |
| [Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean) | `Commute.cfc_real` preserves commutation with an arbitrary other matrix. |
| [Algebra/Algebra/Spectrum/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Algebra/Spectrum/Basic.lean) | `spectrum.zero_notMem_iff` identifies exclusion of zero with native `IsUnit H`. |
| [Basic/Real/Sign.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Basic/Real/Sign.lean) | `Real.sign`, `Real.sign_apply_eq_of_ne_zero`, `Real.sign_zero`, `Real.sign_one`, `Real.sign_neg`. |
| [Algebra/Ring/Commute.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Ring/Commute.lean) | `sq_eq_one_iff` reduces actual real spectral values satisfying λ²=1 to ±1. |

## Selected narrow candidate

Isolated file: `MatrixSpectralSign.lean`, intended canonical destination
`lean/InfoGeometry/Analysis/MatrixSpectralSign.lean`.
Namespace: `InfoGeometry.Analysis.MatrixSpectralSign`.
Carrier: `Matrix n n 𝕜`, with `Fintype n`, `DecidableEq n`, `RCLike 𝕜`.
No nonempty-index assumption is required.

Definition and public theorems:

1. `spectralSign H := cfc Real.sign H`.
2. `spectralSign_isHermitian H`.
3. `spectralSign_eq_spectral hH`: explicit equality to native spectral evaluation.
4. `spectralSign_mul_self hH hunit`.
5. `spectralSign_mul_self_eq_one_iff hH`: invertibility is the exact boundary.
6. `spectralSign_eq_self_of_mul_self hH hsquare`: native sign fixes Hermitian involutions.
7. `spectralSign_commute hcomm`: commutation with H passes to the sign.

The last-but-one theorem lets the integration owner construct a concrete
Hermitian H (for example a Pauli involution), compute its actual CFC sign,
and test the overlap construction without assuming a separate sign matrix.

Direct imports are only the Hermitian matrix calculus, CFC commutation, and
Real.sign owners listed above. There are no repository imports or dependency
pin changes. Source SHA256:
`d6ca43fa50c5913f35542c5f22a48648b316203956edb83457b0c6fb68a79aa2`.
Source review is distinct from compilation; no kernel/axiom/linter acceptance
is claimed in this ledger.

The integration target is the full ordered operator
`D = 1 + Γ * spectralSign H`, with Γ a Hermitian involution and H an
invertible Hermitian matrix, without assuming Γ and H commute. The separate
algebra owner supplies Γ-Hermiticity, Ginsparg–Wilson, modified chirality, and
the chiral intertwiner. Uniform gap, parameter differentiability, locality,
determinant holonomy, gauge anomaly cancellation, and the global measure
construction remain outside this candidate.

## Exact open heads at the last metadata refresh

| [#393](https://github.com/nickgou-nuke/info-geometry-lean/pull/393) | `3fdb21651b265a4997901e74f5174ae1d8fd5636` |
| [#392](https://github.com/nickgou-nuke/info-geometry-lean/pull/392) | `5ddf3e6b50c291d1340eee922e15ae8415d8652a` |
| [#391](https://github.com/nickgou-nuke/info-geometry-lean/pull/391) | `9072e4c10f742659e624f4b8e357e13786744881` |
| [#390](https://github.com/nickgou-nuke/info-geometry-lean/pull/390) | `9bdf62b16183809e58d767bdd95db6ca007e5e1f` |
| [#389](https://github.com/nickgou-nuke/info-geometry-lean/pull/389) | `42aff50c7db9a69caf56c4270b6cd816ef49856b` |
| [#388](https://github.com/nickgou-nuke/info-geometry-lean/pull/388) | `c2afa7486a36d38bb418129d7dc46faf25f1de53` |
| [#387](https://github.com/nickgou-nuke/info-geometry-lean/pull/387) | `2c49fe637666b54cad283102a4ecf9c4d0ca6d51` |
| [#386](https://github.com/nickgou-nuke/info-geometry-lean/pull/386) | `1838b7dfc27cac18937136f6e4c168a8dc314e29` |
| [#385](https://github.com/nickgou-nuke/info-geometry-lean/pull/385) | `e1bbd7950c8d7938beaa8193efdc88937bc15391` |
| [#384](https://github.com/nickgou-nuke/info-geometry-lean/pull/384) | `26b70f741356e387695bd3c9b71694599cb1c2a3` |
| [#383](https://github.com/nickgou-nuke/info-geometry-lean/pull/383) | `5bf5f61c6db0e87e8e249aa95547d9e7fe8b1183` |
| [#382](https://github.com/nickgou-nuke/info-geometry-lean/pull/382) | `138bbde6a635127a831f882f896467450794b5ec` |
| [#381](https://github.com/nickgou-nuke/info-geometry-lean/pull/381) | `192a9a7c6769a18a9c76796afb261555cbda7aa7` |
| [#380](https://github.com/nickgou-nuke/info-geometry-lean/pull/380) | `bc10d8588f97260a3c06a549dff227ebde9b741c` |
| [#379](https://github.com/nickgou-nuke/info-geometry-lean/pull/379) | `fd9e7c9b03ea9a714622638146541f1e97a6bb42` |
| [#378](https://github.com/nickgou-nuke/info-geometry-lean/pull/378) | `8f9ba720b5a674058ff5215f370e50aff165c8d0` |
| [#377](https://github.com/nickgou-nuke/info-geometry-lean/pull/377) | `5bbb5ec97c7c2e6859fd74120a6396e0853fd0b3` |
| [#376](https://github.com/nickgou-nuke/info-geometry-lean/pull/376) | `9c5de41eb003f2ab36cbabe9c176ef6682e1123c` |
| [#375](https://github.com/nickgou-nuke/info-geometry-lean/pull/375) | `555573257c882b7651cb920735c2895f2194238b` |
| [#374](https://github.com/nickgou-nuke/info-geometry-lean/pull/374) | `7fd1f9f8be43e3cd36a4540dce7463430ebcc3a4` |
| [#373](https://github.com/nickgou-nuke/info-geometry-lean/pull/373) | `5498b5fda29ad6182c6aab7e3885837a52a3019e` |
| [#372](https://github.com/nickgou-nuke/info-geometry-lean/pull/372) | `fd4a9f929a99b17adaeb6f8a3d2aa78141285324` |
| [#371](https://github.com/nickgou-nuke/info-geometry-lean/pull/371) | `4922852d7f638f437a7bb1c89f810a6c6e59417b` |
| [#370](https://github.com/nickgou-nuke/info-geometry-lean/pull/370) | `a56bf9e6655c1086d7654b6c4d1eeab705484a5c` |
| [#369](https://github.com/nickgou-nuke/info-geometry-lean/pull/369) | `02f9accbad24efc84158c7f8610f86ff8cfbf093` |
| [#368](https://github.com/nickgou-nuke/info-geometry-lean/pull/368) | `7aa38f6a95230bb8eb6c6d8fe607915c06c853f2` |
| [#367](https://github.com/nickgou-nuke/info-geometry-lean/pull/367) | `39d8f8749bc545bab7d56812aa9f406c157f9809` |
| [#366](https://github.com/nickgou-nuke/info-geometry-lean/pull/366) | `9075e05858bea7fdb8e7f5e7e43f6a6e5d579459` |
| [#365](https://github.com/nickgou-nuke/info-geometry-lean/pull/365) | `80650f9ea87057f10363a723a48c488c630436f9` |
| [#364](https://github.com/nickgou-nuke/info-geometry-lean/pull/364) | `0fc46b2871529ae305d9a0d53258b81728fd818f` |
| [#363](https://github.com/nickgou-nuke/info-geometry-lean/pull/363) | `b2373570829ff9a1722edf0f40c0d67130c090c9` |
| [#362](https://github.com/nickgou-nuke/info-geometry-lean/pull/362) | `853fff86d5997c0f5c315c35366f0f6f390fce18` |
| [#361](https://github.com/nickgou-nuke/info-geometry-lean/pull/361) | `59c72ff4422079295c2b42bde00468fb66ded1b9` |
| [#360](https://github.com/nickgou-nuke/info-geometry-lean/pull/360) | `01cc888565824d2a5f275b28cb33187a28ec6e73` |
| [#359](https://github.com/nickgou-nuke/info-geometry-lean/pull/359) | `c05a07f9aac67233445478bb233e23bee92b73b6` |
| [#358](https://github.com/nickgou-nuke/info-geometry-lean/pull/358) | `473d39724c43ee5cef8ba971ff82dfe42ca084f4` |
| [#357](https://github.com/nickgou-nuke/info-geometry-lean/pull/357) | `681a5c26b82d1c9a547b2b06e760c52ef7ed1908` |

## Superseding concurrent-PR discovery and current reuse

The prior open-PR snapshot was read at 2026-11-17 13:54:55 UTC. PR #395 was created at 13:57:14 UTC, head `7378582cd5a458a39a99ceb8720d04c5a14e3ac1`, on main `08c34e03f610b452e03422037949196dc7d92d6d`. The final publication readback found it and prompted full source inspection.

`InfoGeometry.OperatorAlgebra.GinspargWilson` owns the exact generic two-involution identities; `PeirceTangentTrace` and `RectangularProjectorStabilization` own the adjacent finite trace and stabilization results. No spectral-sign construction is present there. The initial independent generic `Algebra/OverlapDirac.lean` was removed rather than retained as a competing owner.

The new native bridge constructs existing `ChiralInvolution` data with `chi = -spectralSign H`, whose `chi_sq` proof uses `spectralSign_mul_self hH hunit`. It proves compatibility between `1 + Γ * spectralSign H` and upstream `1 - gamma.chi * epsilon.chi`, and between the positive spectral projector and `epsilon.Pright`. It calls the exact upstream declarations `overlapDirac_ginspargWilson`, `ChiralInvolution.Pright_idem`, and `overlapDirac_mul_Pright`. The stronger arbitrary-kernel adjoint and modified-chirality formulas retain their own direct concrete matrix proofs.

PR #394 at `535f52c6554dfc44af5f1e6c4cf1567a8fb6b359` was also inspected at metadata/file-list scope. Its Zorn mobility, entropy-extension, and current work does not supply a competing spectral-sign owner. These new records supersede the earlier absence finding; they are source review, not compiled acceptance.
