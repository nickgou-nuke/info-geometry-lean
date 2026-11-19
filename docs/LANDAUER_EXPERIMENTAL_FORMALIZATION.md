# Landauer experiments and information energy: native formalization

## Result and scope

This extension extracts the mathematical content of the three attached papers
into four focused native Lean/Mathlib owners, containing 26 theorem declarations
and one definition. Independent source review, fresh kernel compilation, axiom
auditing, and source gates passed for the declared selected-module scope. The
validation record below distinguishes this acceptance from the blocked root build.

The main distinction is between entropy loss, a work or heat bound, a change of
stored internal energy, and a proposed rest-mass interpretation. The first two
have precise finite mathematical formulations. The papers do not supply the
extra implication identifying the erasure cost with energy stored in a bit.

The [source/theorem contract](LANDAUER_EXPERIMENTAL_CONTRACT.md) records exact
attachment hashes, carriers, assumptions, owner searches, and role separation.
This work extends the [earlier information-energy formalization](VOPSON_INFORMATION_ENERGY_FORMALIZATION.md)
and uses its full-matrix trace-reset map. It does not change its source.

## Sources

All three supplied PDFs were read in full by the independent source auditor;
the key equations were also checked in rendered pages. Page references below
are PDF page numbers. Vopson's PDF includes a publisher cover, so its printed
article page is one lower. The arXiv version is specifically v1.

1. M. M. Vopson, *The mass-energy-information equivalence principle*,
   AIP Advances 9, 095206 (2019), [DOI 10.1063/1.5123794](https://doi.org/10.1063/1.5123794).
2. A. Berut et al., *Experimental verification of Landauer's principle linking
   information and thermodynamics*, Nature 483, 187-189 (2012),
   [DOI 10.1038/nature10872](https://doi.org/10.1038/nature10872).
3. A. Berut, A. Petrosyan, S. Ciliberto, *Information and thermodynamics:
   Experimental verification of Landauer's erasure principle*,
   [arXiv:1503.06537v1](https://arxiv.org/abs/1503.06537v1) (2015).

The experimental sources concern a controlled colloidal memory. The new
operator results are explicit mathematical extensions of the reset structure;
they are not attributed to these classical experimental papers as quantum
Landauer theorems.

## Causal order of the mathematical statements

| Inputs and existing owners | New proved implication |
|---|---|
| Native binary entropy and existing finite relative entropy | The partial-reset threshold is a uniform-reference entropy deficit, with sharp extrema and monotonicity. |
| Positive normalized finite weights, entropy maximum and its equality case | Exponentiated entropy is bounded by actual finite word count; equality characterizes uniformity. |
| Native finite convexity and an explicit exponential-moment hypothesis | Jensen gives a mean-work lower bound. Actual event/complement sums reconstruct the total mean and produce the binary entropy-deficit bound. |
| Existing trace-reset map and native nondegenerate trace pairing | The backward observable is explicit, and the conserved observables are characterized on the full matrix algebra. |

The heat branch additionally needs the bath entropy relation and a nonnegative
total entropy change. The work branch additionally needs the stated fluctuation
identities. Neither branch supplies a stored-mass or photon-channel hypothesis.

## 1. Binary erasure and relative entropy

Owner: [BinaryErasure.lean](../lean/InfoGeometry/Physics/InformationEnergy/BinaryErasure.lean).
Namespace: `InfoGeometry.Physics.InformationEnergy.BinaryErasure`.

Use Mathlib's native binary entropy, in nats:

\[
h(p)=-p\log p-(1-p)\log(1-p).
\]

`entropyOf_binary` connects the existing finite Shannon functional on
`![p, 1-p] : Fin 2 -> Real` with `Real.binEntropy p`. This includes endpoints
through Mathlib's total logarithm convention; physical probability statements
retain the domain `0 <= p <= 1`.

The sole new definition is

\[
L(k_B,T,p)=k_BT[\log2-h(p)].
\]

`erasureCost_eq_relativeEntropy` identifies this with
`kB*T*finiteRelativeEntropy q u`, where `q = (p,1-p)` and `u = (1/2,1/2)`.
This bridge requires `0 < p < 1`, matching the existing strictly positive
finite relative-entropy owner's hypotheses. The endpoint theorems use native
binary entropy directly and do not apply that positive-weight API at zero.

The remaining results establish:

- `erasureCost_bounds`: for nonnegative `kB,T` and `p` in `[0,1]`,
  `0 <= L <= kB*T*log 2`.
- `erasureCost_eq_zero_iff`: for positive `kB,T`, zero threshold occurs exactly
  at `p = 1/2`.
- `erasureCost_eq_full_iff`: for positive `kB,T`, the full threshold occurs
  exactly at the deterministic endpoints `p = 0` or `p = 1`.
- `erasureCost_strictMonoOn`: the threshold strictly increases on `[1/2,1]`
  when `kB,T` are positive.
- `erasureCost_complement`: choosing the opposite target bit leaves the
  entropy-loss threshold unchanged.

The heat interface is an exact equivalence for `T > 0`:

\[
0\le k_B[h(p)-\log2]+Q/T
\quad\Longleftrightarrow\quad
L(k_B,T,p)\le Q.
\]

This is `entropy_balance_iff_heat_bound`. Its premise expresses the memory
entropy change plus bath entropy change. The theorem does not derive the bath
relation `Delta S_bath = Q/T` from dynamics or certify experimental heat data.
In the application, `Q` is heat delivered to the bath and is an ensemble mean.
It is not asserted to be a lower bound on each individual trajectory.

## 2. Effective count versus actual cardinality

Owner: [EffectiveStateCount.lean](../lean/InfoGeometry/Physics/InformationEnergy/EffectiveStateCount.lean).
Namespace: `InfoGeometry.Physics.InformationEnergy.EffectiveStateCount`.

Let `q` be strictly positive normalized weights on a nonempty finite type `A`.
The existing `entropyOf q` is reused without a new Shannon definition. For a
natural word length `N`, the actual state count is

\[
|\operatorname{Fin}(N)\to A|=|A|^N.
\]

The new comparison proves

\[
\exp(NH(q))\le |A|^N.
\]

For `N > 0`, equality holds exactly when every weight is `1/|A|`; nonuniform
weights give a strict inequality. The exact declarations are
`word_count_eq_exp`, `effectiveCount_le_word_count`,
`effectiveCount_eq_word_count_iff_uniform`, and `effectiveCount_lt_word_count`.
The positivity assumption makes the entire finite carrier the support.

For an interior, nonuniform binary law, the stronger single-copy statements are

\[
1<\exp(h(p))<2,
\qquad
\forall m\in\mathbb N,\quad \exp(h(p))\ne m.
\]

These are `binary_effectiveCount_between` and `binary_effectiveCount_not_nat`.
They expose the precise problem with interpreting Vopson 2019 Eq.(3) as a
literal count for arbitrary weights. For `p=1/4`, ordinary numerical evaluation
gives approximately `1.75476535`, while two outcomes remain possible. That decimal
is illustrative numerical evaluation, not a certified decimal approximation.

The word-count comparison takes `N*H(q)` as the supplied additive-entropy
expression. It does not construct a stochastic product process or prove an
independence assumption. Its cardinality side is the actual native finite
function type. The single-copy nonintegrality theorem is not generalized to
arbitrary word lengths or other alphabets.

## 3. Finite fluctuation moments and conditioned work

Owner: [Jarzynski.lean](../lean/InfoGeometry/Physics/InformationEnergy/Jarzynski.lean).
Namespace: `InfoGeometry.Physics.InformationEnergy.Jarzynski`.

The implementation uses `Finset.centerMass` and finite sums, not a parallel
expectation structure. For nonnegative weights with positive total mass,
positive inverse temperature `beta`, and a positive moment bound `A`, native
Jensen proves

\[
\mathbb E[e^{-\beta W}]\le A
\quad\Longrightarrow\quad
\mathbb E[W]\ge-\frac{\log A}{\beta}.
\]

`neg_log_expMoment_le_centerMass` proves this general statement.
`mean_work_ge_of_jarzynski` specializes it to normalized weights and the explicit
identity `E(exp(-beta W)) = exp(-beta DeltaF)`, obtaining `DeltaF <= E(W)`.
The physical fluctuation identity is a hypothesis; it is not defined to be its
own answer.

`expectation_entropyProduction_nonneg` uses a substantive existing owner:
`DirectedThermoGraph.IntegralFluctuationLaw` in
`Canonical/ThermodynamicChiralGraphCalculus.lean`. That owner has strictly
positive normalized forward and reverse finite laws, defines entropy production
as their log-ratio, and proves the exponential identity by reverse normalization.
The new theorem derives its nonnegative forward mean by Jensen.

For reset, an actual predicate partitions a finite ensemble into success and
failure. `sum_eq_conditioned_mixture` derives the law of total expectation from
the two filtered sums. With success mass `0 < p < 1`, assume the two conditional
identities from the symmetric cyclic setting:

\[
\mathbb E[e^{-\beta W}\mid S]=\frac{1}{2p},\qquad
\mathbb E[e^{-\beta W}\mid S^c]=\frac{1}{2(1-p)}.
\]

`conditioned_mean_work_lower_bound` gives the success bound
`(log 2 + log p)/beta`; its complement gives `(log 2 + log(1-p))/beta`.
`partition_moments_imply_work_bound` then proves both

\[
\mathbb E[e^{-\beta W}]=1,\qquad
\mathbb E[W]\ge\frac{\log2-h(p)}{\beta}.
\]

`mean_work_ge_erasureCost_of_conditional_moments` converts the last result to
`erasureCost kB T p` under the explicit relation `beta^{-1}=kB*T`.

The assumptions are mathematically satisfiable: a two-outcome ensemble with
weights `p,1-p` and work values `beta^{-1}log(2p)` and
`beta^{-1}log(2(1-p))` attains these expressions. This is the independent
auditor's non-vacuity check, not an added theorem about physical achievability.

In arXiv v1, this `p` is `P_Sforce`, measured when the force stops, before the
barrier is restored. It is distinct from final-cycle success `P_S`. An exact
perfect-success endpoint cannot be inserted into the failure denominator: a
zero-probability group cannot supply the required positive unnormalized
exponential mass. Rare failures matter to the exponential average. Continuous
trajectory measures, Langevin solutions, stochastic work integrals, and limiting
perfect-erasure protocols remain outside these finite results.

## 4. Noncommuting matrix observables under reset

Owner: [ObservableErasure.lean](../lean/InfoGeometry/Physics/InformationEnergy/ObservableErasure.lean).
Namespace: `InfoGeometry.Physics.InformationEnergy.ObservableErasure`.

The carrier is the full finite matrix algebra over a field. For the existing
native reset `R_sigma(X)=tr(X)*sigma`, the new trace pairing is

\[
\operatorname{tr}(R_\sigma(X)H)
=\operatorname{tr}\!\left(X[\operatorname{tr}(\sigma H)I]\right).
\]

`trace_reset_pairing` preserves the ordered products. Native trace-pairing
nondegeneracy gives `trace_reset_conserved_iff`. With `tr(sigma)=1`,
`trace_reset_conserved_iff_scalar` characterizes conservation against every
matrix input exactly by `H=c I` for some scalar `c`. Scalarity is the conclusion
of the conservation theorem, not an assumption replacing the operator problem.
The statement quantifies over all matrices, not merely density matrices.

`noncommuting_reset_equal_energy` constructs

\[
H=\begin{pmatrix}5&1\\1&1\end{pmatrix},\quad
\rho=\begin{pmatrix}3/4&0\\0&1/4\end{pmatrix},\quad
\sigma=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\]

All three are positive semidefinite; the states have trace one. The theorem
proves `rho*rho != rho`, `sigma*sigma = sigma`, and all three pairwise
noncommutation statements. Reset sends `rho` to `sigma`, yet their energy
expectations agree. Their displayed entries give `tr(rho H)=tr(sigma H)=4`.
The positivity proofs use native diagonal positivity and Gram factorizations;
the actual matrices and their products are never replaced by scalar spectra.

`positive_trace_one_noncommuting_pair` exposes the two states as a standalone
native existence theorem, including positivity, trace normalization, and the
mixed/pure conditions. This makes the noncommutativity of density matrices
directly reusable without carrying the Hamiltonian data.

This proves a state change can preserve a particular energy expectation under
a nonscalar Hamiltonian. It does not assert a zero heat cost. A bath,
system-bath dynamics, entropy production, and the first law are separate
structures. The earlier `EnergyAccounting.heat_bound_does_not_force_internal_energy_loss`
owner already supplies the first-law countermodel `W=Q`, `DeltaU=0` and is not
duplicated here.

## 5. Source corrections and interpretation boundaries

| Source location | Finding and treatment |
|---|---|
| Vopson 2019, PDF p.3, sections I-II | The printed entropy and heat inequalities use `<=`. Its own `DeltaS_total >= 0` premise implies the lower bound `>=`. The new entropy-balance theorem derives the corrected direction. Equality needs an additional reversible-limit condition. |
| Vopson 2019, PDF p.2, Eq.(3) | `2^(N H_bits)` is generally an effective count. The new native cardinality comparison identifies the uniformity condition. |
| Vopson 2019, PDF pp.3-4, Eq.(6) | Assigning `kBT log2` as stored bit energy is an additional hypothesis. The paper expressly restricts its proposal to classical equilibrium digital memories; it excludes relativistic carriers and photons. |
| Vopson 2019, PDF p.4 | A vanishing temperature-dependent mass formula does not imply that a binary state space or its Shannon entropy ceases to exist at zero temperature. |
| Vopson 2019, PDF p.5 | The notation `1Tb` is followed by `10^12 bytes = 8*10^12 bits`. Its mass estimate therefore uses a decimal terabyte, not a terabit. |
| Nature 2012, PDF p.4, Methods | The calculation uses mean `DeltaU=W-Q=0`, so work supplies the heat. Returning the control parameters alone would not prove this for arbitrary nonequilibrium endpoint distributions. |
| Berut 2015, pp.11-13 and 17 | Final success and success at force termination are distinct. Success-conditioned heat is used as an approximation near perfect erasure; the exact finite theorem retains the conditioning and probability factors. |
| Berut 2015, p.10 | A purported quadratic potential is printed as `-k(I)x`, a linear expression. The following force `-kx` corresponds to `kx^2/2` up to an additive constant. |
| Berut 2015, p.11 | The printed omitted heat `0.7 kBT` is called 10% of `kBT log2`, but `0.7/log2` is about 1.01, or 101%. The decimal is not silently changed to `0.07`. |
| Berut 2015, p.17, Eq.(28) | A negative logarithm of an exponential average is dimensionless. Physical effective free energy requires the factor `beta^{-1}`, unless units of `kBT` are explicitly adopted. |

The decimal ratio above is ordinary numerical checking, not a certified Lean
decimal bound. The source errors were confirmed visually, not inferred only
from extracted PDF text.

The experiments measure dissipation of a controlled operation. They do not
measure an information rest mass. The 2019 stored-mass proposal and the later
2022 elementary-particle/radiation proposal add separate assumptions. None of
the new finite entropy, Jensen, or trace-pairing theorems derives those
assumptions, an emission channel, a photon count, or a detector model.

## 6. Validation record

Status: **ACCEPTED_WITH_LIMITED_SCOPE** on 2026-11-16. Independent mathematical
review and fresh kernel/axiom validation passed for the four new owners and
their exact 13-module repository source closure. The maintained audit also
checks generated auxiliaries, for 46 declarations in total.

| New owner | Theorems | Definitions | Audited declarations | New-source warnings |
|---|---:|---:|---:|---:|
| BinaryErasure | 8 | 1 | 13 | 0 |
| EffectiveStateCount | 6 | 0 | 7 | 0 |
| Jarzynski | 7 | 0 | 15 | 0 |
| ObservableErasure | 5 | 0 | 11 | 0 |
| **Total** | **26** | **1** | **46** | **0** |

All 13 closure modules compiled successfully, with every module recorded as
`reused=false`. The axiom audit returned zero and reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. No proof holes, custom axioms,
`native_decide`, or gate suppressions were introduced.

The toolchain is Lean `v4.34.1`, with unchanged Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The one initially missing native
binary-entropy import was recovered from the cache for that exact pin; no
dependency source, version, or gate was modified.

The maintained source-closure check is:

```bash
python3 -B tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/64554963d837/mathlib-4.34.1 \
  --lean /workspace/scratch/64554963d837/lean-runtime/bin/lean \
  --output /workspace/scratch/9eb3301f34a1/landauer/verification-independent \
  --target InfoGeometry.Physics.InformationEnergy.BinaryErasure \
  --target InfoGeometry.Physics.InformationEnergy.EffectiveStateCount \
  --target InfoGeometry.Physics.InformationEnergy.Jarzynski \
  --target InfoGeometry.Physics.InformationEnergy.ObservableErasure
```

This check compiles the actual repository import closure against the pinned
native Mathlib and audits every declaration introduced by the four target
modules. Final acceptance ran without `--incremental` or `--skip-audit` into a
fresh output tree. It is distinct from a whole-root Lake build.

The fresh run reported five existing unused-section-variable warnings: two in
`Inference.FiniteRelativeEntropyEquality` and three in
`Inference.FiniteGibbsThermodynamicIdentity`. Those pre-existing owners remain
unchanged. The four new owners and the axiom audit produced zero warnings.

Independent source/mathematical audit was performed by `paper_audit`, which did
not write the Lean owners. Independent fresh compilation, axiom and gate review
was performed by `repo_survey`, which did not write theorem content or act as the
source auditor. Generation and acceptance are distinct roles.

### Source gates and corrective action

| Check | Final result |
|---|---|
| Strict placeholder audit, each new owner | Four exits 0; no proof holes. |
| Semantic vacuity gate, `--fail-on error` | Exit 0; no errors. |
| OpenGauss screener, `--strict` | Exit 0; no violations. |
| OpenGauss refutation, `--strict` | Exit 0; no traps. |
| Static Gate 4, each new owner | Four exits 0; no holes, traps, or scope warnings. |
| Integration and whitespace checks | Verified sources match the staged index; exactly four imports added to `InfoGeometry.All`; staged and unstaged diff checks clean. |

The placeholder audit's short-proof advisory for `entropyOf_binary` and the
semantic gate's advisory for `erasureCost_complement` were independently
reviewed. The first is a legitimate bridge between independently owned entropy
expressions; the second transports native binary-entropy symmetry. Neither
assumes its proposed conclusion.

An initial strict T16 check could not recognize the richer three-matrix
existential witness. The correction added
`positive_trace_one_noncommuting_pair`, a proved projection retaining positive
semidefiniteness, trace-one normalization, noncommutation, and the mixed/pure
conditions. The richer theorem was preserved. Final strict checks passed;
no checker, filter, suppression, or physical assumption was changed.

The static Gate 4 verdict is `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`: that tool
performs source review only. The separate fresh compiler and axiom audit above
supply the kernel evidence. These receipts are not interchangeable.

The independent evidence directory is the output path in the command above.
Its `qa-final.json` records limited-scope acceptance; `report.json` and
`axioms.log` record the kernel results; `qa-gates-final.json`,
`qa-gate4-combined.json`, `qa-semantic-review-final.json`, and
`qa-integration-final.json` record the remaining checks. The initial T16
receipt is retained alongside its correction. The commit workflow additionally
runs the installed staged-source pre-commit hook.

### Verified source hashes

These are SHA-256 hashes of the exact four source files accepted by the
independent reviewer, compiler, axiom audit, and final gates.

| Owner | SHA-256 |
|---|---|
| BinaryErasure.lean | `4c77235fbb4236a9802273620a11791dcea1633c2e1a5fb5840b61a87d627e83` |
| EffectiveStateCount.lean | `95424287759467bc914915c470f579a720f6a10e24138ebc1a13f030e33139b5` |
| Jarzynski.lean | `1b5d6ca08be6d4a5533d487fc834a8984c7629d1a495ee9ce6d3ac58e6519287` |
| ObservableErasure.lean | `43d98e7f9a9b3d8c6d3fe70bdb4198e7a981d93b2657e88fa29aaf86386f1cfd` |

### Root build limitation

The current `tools/infra/ci_bootstrap.py paths` preflight returned exit 1.
Atlas and HomotopyHypothesis lack their path-package configuration files and
are untracked dependencies. GIFT is an uninitialized gitlink pinned at
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92`, also missing its configuration.
InfoGeometryCore passed this path preflight. The exact receipt is
`root-path-preflight.json`; this check concerns package availability and
provenance, not transitive compilation.

Dependency pins, verification helpers, gates, and hooks remain unchanged.
The complete root Lake build and the rest of `InfoGeometry.All` are not
certified. The root publication/build gate has not passed; this continuation
is published as a draft with the selected-module certificates and these
existing dependency blockers disclosed.
