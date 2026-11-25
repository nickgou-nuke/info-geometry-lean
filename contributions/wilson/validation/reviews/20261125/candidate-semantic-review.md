# Independent semantic review of Gaussian Markov and reflection bridges

**Verdict: PASS at the source level, reconciled with successful exact-destination CI.** No mathematical change is required in the three reviewed owner modules. Semantic review and compiler/axiom acceptance are separate evidence: this reviewer inspected the final sources and independently reconciled them with the successful CI artifacts, without running Lean or Lake. Review date: 2026-11-25.

## Reviewed source snapshot

Paths below are relative to `contributions/wilson/gaussian/` at source commit [`ff8e1632b45569d88da1c73c0ec160c913fe55f9`](https://github.com/nickgou-nuke/info-geometry-lean/commit/ff8e1632b45569d88da1c73c0ec160c913fe55f9). These hashes also match the current preparation-package Lean files and the exact CI source inventory.

| Owner | SHA-256 | Public theorems | Audit entries |
| --- | --- | ---: | ---: |
| `GaussianBlockSpin/WeightedMarkovKernel.lean` | `350eea7735ba80d6cff36387a7658f0f4989fc1fe15168fd0b3581d60591ec9b` | 11 | 13 |
| `GaussianBlockSpin/ReflectionPositiveCovariance.lean` | `60895362740af4a57657f84e891dd72e57d87a87add9eec045468c0f4a7a44da` | 12 | 12 |
| `GaussianBlockSpin/WeightedReflectionPositive.lean` | `2d35164841286342645bc373a777c4c84d7d6c0c7ff569574de5f83de6e570bd` | 1 | 1 |

The Markov audit additionally covers the kernel definition and its Markov instance. The three new owners contribute **24 public theorems and 26 audit entries**. The complete Gaussian contribution contains **78 public theorems and 80 audit entries**, including its earlier weighted-elimination owners. All 80 reports are present in the fresh successful CI transcript. If a later code edit changes these owner hashes, reconcile that diff and its validation before carrying this acceptance forward.

The final source reconciliation includes the KL documentation clarification, native real-order import and proof repairs, the explicit positive-time projection noncommutativity witness, and the name `weightedMarkovKernel_apply_set`. Replacing only that final name by the earlier `weightedMarkovKernel_apply'` reproduces the previously reviewed Markov source hash `212f582fb22a11c30175c28feea885dea3d3cb88f00985bde95e713c21637f45` exactly. The rename changes no proposition or proof operation. The earlier separate preview-contract hashes are superseded by the integrated package inventory; they are not used as evidence for the final code.

## Exact destination CI reconciliation

[Run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500), at the source commit above, passed all four destination jobs. The detailed Gaussian evidence is [job 139058006800](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500/job/139058006800), targeting upstream `c25e77e9654a54fc5e4a04bfb637b7144defacc0`. The reviewer independently queried the GitHub job results and confirmed that compilation, fresh axiom-transcript generation, and source/pin/axiom verification each succeeded.

The retained [artifact receipt](../../evidence/exact-gaussian-ff8e163/artifact-receipt.json), [source inventory](../../evidence/exact-gaussian-ff8e163/source-inventory.json), and [axiom audit](../../evidence/exact-gaussian-ff8e163/axiom-audit.json) identify the checked artifact and declarations. Independent local reconciliation established:

- All **15 Gaussian Lean source and audit files** match the SHA-256 values in the CI inventory, including the three owners above and the combined `WeightedCoarseGrainingAudit.lean`.
- The current combined audit, CI expected-declaration inventory, raw fresh `axioms.log`, and parsed audit JSON contain exactly the same **80 unique declaration names**, with no missing, duplicate, or extra report.
- Every report lists only `propext`, `Classical.choice`, and `Quot.sound`. Both `weightedMarkovKernel_apply_set` and `reflection_not_commute_positiveTime_projection` are included.
- The retained build log ends with successful completion. The checked-in workflow uses `lake --wfail build GaussianBlockSpin.WeightedCoarseGrainingAudit` and separately runs `lake env lean GaussianBlockSpin/WeightedCoarseGrainingAudit.lean` for the fresh transcript. This establishes the focused audit and its import closure, not a full build of every upstream project.
- All nine recorded dependency revisions agree with the artifact's resolved manifest, including the exact Mathlib revision stated below. The CI verification step also passed its unchanged-configuration and source-hash checks.

For workflow context, the four recorded candidate inventories are Gaussian **78/80**, cutoff **16/16**, Gram **27/29**, and states **10/11**, where each pair is public theorems / axiom reports: **131 theorems and 136 reports** in total. The detailed source reconciliation in this section covers the Gaussian contribution; the other three counts come from their corresponding successful-run inventories and audits.

## Native dependency contract

The target Gaussian package uses Lean `v4.34.0-rc2` and Mathlib revision `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`. The earlier source review read the actual pinned Mathlib files in the build checkout, and the final CI artifacts record the same versions. The native owners reviewed include:

- [`Kernel.WithDensity`](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/Probability/Kernel/WithDensity.lean): `withDensity`, `withDensity_apply`, and `lintegral_withDensity`.
- [`Kernel.Basic`](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/Probability/Kernel/Basic.lean): the s-finite constant-kernel instance.
- [`Kernel.Composition.Comp`](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/Probability/Kernel/Composition/Comp.lean): `lintegral_comp`.
- [`KullbackLeibler.Basic`](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/InformationTheory/KullbackLeibler/Basic.lean): the extended, mass-corrected `klDiv` definition.
- [`KullbackLeibler.DataProcessing`](https://github.com/leanprover-community/mathlib4/blob/8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a/Mathlib/InformationTheory/KullbackLeibler/DataProcessing.lean): `klDiv_comp_right_le` and its section-level assumptions `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`.

## Markov adapter: PASS

The carrier is the native finite-dimensional real `EuclideanSpace ℝ n`, with finite coordinate types and canonical Borel/Lebesgue structures. The inherited density takes **output before input**, `weightedBlockKernel R hR Q ψ φ`; the bundled native kernel correctly maps fine input `φ` to a measure on coarse output `ψ`.

The construction uses the constant Lebesgue kernel and `Kernel.withDensity`. This native definition has a zero fallback for a density that is not jointly measurable. The candidate proves joint continuity and joint `ENNReal.ofReal` measurability, then proves `weightedMarkovKernel_apply` by the measurable branch theorem. Consequently its measure readback genuinely equals `volume.withDensity`; the fallback is not silently admitted.

Normalization is proved from the existing Gaussian real integral. Deriving integrability from a real integral equal to one is legitimate: Mathlib's totalized Bochner integral would be zero for a nonintegrable function. Positivity then converts the real normalization to a `lintegral` of one. The Markov instance therefore follows from an actual probability mass calculation for every input.

The composite kernel has input-to-output order `κ₂ ∘ₖ κ₁`. Its observation map is `Q₂ * Q₁` and noise precision is `coarsePrecision R₁ R₂ Q₂`, whose inverse is

\[
R_2^{-1}+Q_2R_1^{-1}Q_2^{\mathsf T}.
\]

The proof uses the already proved real density convolution, nonnegativity, Tonelli, and the native kernel integral formula. It establishes equality of bundled kernels, not only equality of unbundled densities. Measurable nonnegative test functions may have infinite integrals; the proof does not assume a missing integrability hypothesis for those tests. No rank or nonempty-coordinate assumption is introduced.

The KL theorem applies the **same** Markov kernel to two finite input measures and directly instantiates Mathlib's data-processing theorem. It does not assume the input divergence is finite, nor does it claim a strict contraction factor.

**Documentation clarification incorporated:** for arbitrary finite measures, pinned `InformationTheory.klDiv` includes the mass correction `ν.real univ - μ.real univ` and takes values in `ℝ≥0∞`. For probability measures this specializes to ordinary relative entropy. The theorem documentation now states this distinction. Publication prose should retain it.

## Finite covariance reflection owner: PASS

Let `C` be the fine covariance, `N` the coarse noise covariance, `Q` the observation matrix, and `Uf`, `Uc` test maps. Dimensions are correct for `B : Matrix p q ℝ` in

\[
\theta_cQ=Q\theta_f,\qquad Q^{\mathsf T}U_c=U_fB.
\]

These hypotheses give exactly

\[
U_c^{\mathsf T}\theta_c(N+QCQ^{\mathsf T})U_c
=U_c^{\mathsf T}\theta_cNU_c
+B^{\mathsf T}(U_f^{\mathsf T}\theta_fCU_f)B.
\]

Transpose orientation is correct: transposing the test-transport identity gives `Ucᵀ * Q = Bᵀ * Ufᵀ`. Native positive-semidefinite congruence and addition prove the conclusion from **separate fine and noise reflection-form positivity** assumptions.

The algebraic identity does not require the matrices called `θ` to be involutions or symmetric. For an application with the conventional form `⟨θ f, C f⟩`, instantiate symmetric orthogonal involutions; the theorem contract explicitly distinguishes this physical interpretation from the more general matrix identity. The test maps need not be injective. An actual positive-time inclusion is an application-specific choice, and the transport hypothesis expresses the needed support compatibility.

The counterexample is substantive. With the swap reflection, positive-time test `e₁`, and

\[
N=\begin{pmatrix}1&-1/2\\-1/2&1\end{pmatrix},
\]

`N` is positive definite and commutes with reflection, but the compressed reflected form is `-1/2`. The identity covariance is reflection positive on the same test space. Identity blocking with noise `N` produces `I + N`, still positive definite and reflection commuting, but not reflection positive on that test space. Thus the omitted noise assumption cannot be repaired by ordinary positivity or commutation alone.

The added native definition `positiveTimeProjection := positiveTime * positiveTimeᵀ` is the coordinate projection `P = diag(1,0)`. The new theorem `reflection_not_commute_positiveTime_projection` is meaningful and correct: the `(0,1)` entry of `θ * P` is zero, whereas the same entry of `P * θ` is one. Its contradiction proof reads that exact matrix entry. This makes explicit that reflection exchanges the two halves even though the covariance can commute with reflection. It does not add or weaken a hypothesis of the transport theorem.

The source-proxy staged gate was a separate preparation check. The final exact-destination CI now supplies the previously pending compiler evidence for the projection witness: its declaration appears in the successful fresh 80-report transcript, and its owner hash matches the inventory. The staged gate itself is not treated as a compiler certificate.

## Actual Schur precision adapter: PASS

`WeightedReflectionPositive.lean` imports the real coarse-graining owner and applies its existing `coarsePrecision_inv` theorem. It uses fine covariance `A⁻¹` and noise covariance `R⁻¹`, under `A.PosDef` and `R.PosDef`, and concludes positivity of the compressed reflected form of `(coarsePrecision A R Q)⁻¹`.

This is an adapter to the actual precision definition. It introduces no surrogate Schur operator and does not confuse precision positivity with covariance reflection positivity. The real conjugate-transpose to transpose conversion is the correct specialization.

## Scope of acceptance

These sources establish a native finite-dimensional Gaussian Markov calculus, extended KL data processing, and a finite matrix criterion for reflected covariance positivity. They do not establish a Gaussian-measure OS theorem for all positive-time nonlinear observables, gauge coercivity, strict Fisher/KL contraction, a `c`- or `a`-theorem, a continuum limit, a full nonlinear Yang–Mills minimizer, or a Lorentzian Hilbert space/Hamiltonian reconstruction. The owner comments and theorem contracts preserve this boundary.

## Preparation-source interface reconciliation

The final preparation package renames only the set-probability readback theorem from
`weightedMarkovKernel_apply'` to `weightedMarkovKernel_apply_set`, including its
uses and audit entry. This makes the measure/set distinction explicit and
retains the existing strict audit parser unchanged. No proposition or proof
operation changes. The exact byte-level rename comparison, final source hashes,
and fresh audit name were independently verified as described above.
