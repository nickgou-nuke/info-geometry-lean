# Chiral reciprocity, bounded inverse obstructions, and exponential traces

## Result and provenance

This continuation extracts precise operator statements from
`Pasted text(20261116-170755).txt` and separates them from its unsupported
topological and physical conclusions. The selected native Lean owners concern
actual Hilbert-space eigenspaces, the existing closed-range Moore-Penrose
construction, and genuine normed-algebra exponentials. Their theorem contract
is [CHIRAL_RECIPROCITY_CONTRACT.md](CHIRAL_RECIPROCITY_CONTRACT.md).

The source attachment has 254 lines and SHA-256
`049da78bfe67a287774ce409a3a41f793992a72c987b8502667a43f1960afc69`.
Its first-person narrative and psychological interpretations are not
mathematical evidence. The original attachment is preserved; no claim about
the user's psychology is part of this formalization.

The branch starts at upstream `main`, commit
`08c34e03f610b452e03422037949196dc7d92d6d`, independently of the earlier
reconstruction/Landauer PR. The environment remains Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

**Validation status: independent QA accepted the three selected owners.**
Fresh native compilation and axiom auditing, strict source checks, and static
Gate 4 passed. Root dependency availability remains blocked as documented
below; these results do not establish a whole-repository build.

## 1. Positive Gram eigenspaces have an actual reciprocal isometry

Owner: [HilbertGramReciprocity.lean](../lean/InfoGeometry/Analysis/HilbertGramReciprocity.lean).

Let `E,F` be complete real or complex Hilbert spaces and let `A : E →L[𝕜] F`
be an arbitrary bounded linear map. Write

$$
G_E=A^*A,\qquad G_F=AA^*.
$$

The eigenspaces are native `Module.End.eigenspace` submodules of these actual
compositions. No matrix representation, dimension equality, eigenbasis, or
compactness hypothesis is introduced.

The existing
[HilbertGramDuality](../lean/InfoGeometry/Analysis/HilbertGramDuality.lean)
owner supplies a continuous linear equivalence at each nonzero scalar
eigenvalue, with forward map `A` and inverse `μ⁻¹ A*`. It also proves

$$
\langle Ax,Ay\rangle=\mu\langle x,y\rangle
\quad\text{when }G_Ey=\mu y.
$$

The new owner first uses an actual nonzero eigenvector to derive

$$
\mu=\frac{\|Ax\|^2}{\|x\|^2}\in[0,\infty).
$$

Thus an actual Gram eigenvalue is real and nonnegative, and a nonzero one is
strictly positive. The `HasEigenvalue` premise is essential here: a named
scalar or a zero vector does not establish positivity.

For a real `r > 0`, the new construction is the native `LinearIsometryEquiv`

$$
U_r:\operatorname{Eig}(G_E,r)\simeq_{\mathrm{isom}}
\operatorname{Eig}(G_F,r),\qquad
U_rx=\frac{Ax}{\sqrt r},\qquad
U_r^{-1}y=\frac{A^*y}{\sqrt r}.
$$

It normalizes the existing equivalence and proves inner-product preservation;
norm preservation is not a stored assumption. Applying the normalized
construction to `A.adjoint` gives the inverse construction after the explicit
native adjoint-involution transport.

| New declaration | Exact role |
|---|---|
| `gram_eigenvalue_real_nonneg` | Reality and nonnegativity from an actual eigenvalue witness. |
| `gram_eigenvalue_re_pos` | Strict positivity when that actual eigenvalue is nonzero. |
| `normalizedGramEigenspaceEquiv` | Constructed native linear isometric equivalence. |
| `normalizedGramEigenspaceEquiv_apply` | Forward action `A / sqrt r`. |
| `normalizedGramEigenspaceEquiv_symm_apply` | Inverse action `A.adjoint / sqrt r`. |
| `normalizedGramEigenspaceEquiv_adjoint_apply` | Adjoint exchange agrees with inversion. |

The existing specialized normalization in
`Canonical.RealCl55NativeChiralHodgeIndexBridge` concerns fixed chiral sectors
and a fixed scalar. It is not replaced. The new carrier is the arbitrary
native Gram eigenspace, including infinite-dimensional ambient Hilbert spaces.

## 2. Moore-Penrose reciprocity supplies a quantitative obstruction

Owner: [HilbertGramMoorePenrose.lean](../lean/InfoGeometry/Analysis/HilbertGramMoorePenrose.lean).

For `A : E →L[𝕜] F` and `B : F →L[𝕜] E`, the reused
`Singular.MoorePenrose.IsMoorePenroseInverseCLM A B` consists of the four
typed operator equations

$$
ABA=A,\quad BAB=B,\quad(AB)^*=AB,\quad(BA)^*=BA.
$$

The existing [MoorePenrose owner](../lean/InfoGeometry/Singular/MoorePenrose.lean)
constructs such a bounded `B` when `range A` is closed. It restricts `A` to
the orthogonal complement of its kernel, uses the bounded inverse theorem
onto its range, and composes with the range's orthogonal projection. The new
work consumes this construction; it does not introduce an assumption-only
replacement for the inverse.

The first and fourth equations alone give

$$
BAA^*=A^*.
$$

This is the typed Hilbert-operator counterpart of Penrose's original Eq. (8)
[S1]. If `AA*y = μy` with `μ ≠ 0`, applying that identity gives

$$
By=\mu^{-1}A^*y.
$$

For real `r > 0`, comparison with the isometry above yields

$$
U_r^{-1}y=\sqrt r\,By,
\qquad
\|By\|=\frac{\|y\|}{\sqrt r}.
$$

For an actual nonzero eigenvector, the bounded-operator estimate
`‖By‖ ≤ ‖B‖ ‖y‖` permits cancellation of `‖y‖` and gives

$$
1\le r\|B\|^2.
$$

Consequently, the explicit point-spectrum hypothesis

$$
\forall\varepsilon>0\;\exists r\in(0,\varepsilon),\quad
r\text{ is an eigenvalue of }AA^*
$$

implies that `range A` is not closed. Otherwise the existing closed-range
construction would supply a bounded `B`. Taking
`ε = 1 / (‖B‖² + 1)` contradicts the preceding inequality. This choice avoids
dividing by a possibly zero operator norm.

| New declaration | Exact role |
|---|---|
| `comp_adjoint_eq_of_inner_inverse` | Absorption `BAA*=A*` from the two needed equations. |
| `apply_eq_inv_smul_adjoint_of_mem_eigenspace` | Reciprocal action on a nonzero eigenspace. |
| `moorePenroseInverse_apply_of_mem_eigenspace` | Specialization to the actual closed-range construction. |
| `normalized_symm_eq_sqrt_smul` | Compatibility with the normalized inverse isometry. |
| `norm_apply_of_mem_eigenspace` | Exact inverse norm scaling. |
| `one_le_eigenvalue_mul_norm_sq` | Quantitative lower bound from an actual eigenvalue. |
| `not_isClosed_range_of_positive_eigenvalues_arbitrarily_small` | Point-spectrum obstruction to closed range. |

The last theorem is one-way. It does not say that every failure of closed
range has point eigenvalues tending to zero. It constructs neither a complete
spectral resolution nor an unbounded pseudoinverse. The obstruction concerns
small positive eigenvalues; large energies do not cause this reciprocal norm
to blow up.

## 3. Cyclicity extends algebraic cancellation to actual exponentials

Owner: [GradedExponentialTrace.lean](../lean/InfoGeometry/Analysis/GradedExponentialTrace.lean).

Let `𝒜` be a complete normed associative algebra over a real or complex
scalar field. Let `τ : 𝒜 →L[𝕜] 𝕜` be a continuous linear functional with
`τ(XY)=τ(YX)`. If

$$
\Gamma D+D\Gamma=0,
$$

then for every scalar `t`,

$$
\boxed{\tau\!\left(\Gamma\exp(tD^2)\right)=\tau(\Gamma).}
$$

The theorem does not require `Γ²=1`, a star operation, self-adjointness, or
positivity. In the general statement `Γ` is an anticommuting weight. The
concrete matrix specialization below uses an actual grading involution.

The proof has two separate steps. First, `D` commutes with every power of
`D²`, so `Γ(D²)^k` still anticommutes with `D`. The existing
[NoncommutativeGradedTrace](../lean/InfoGeometry/OperatorAlgebra/NoncommutativeGradedTrace.lean)
owner then proves

$$
\tau\!\left(\Gamma(D^2)^{k+1}\right)=0.
$$

Second, native `NormedSpace.exp_series_hasSum_exp'` supplies convergence of the
actual exponential series. The continuous functional `X ↦ τ(ΓX)` transports
that `HasSum`; all positive-degree coefficients vanish, and the degree-zero
term is `τΓ`. This is not an equality about an unverified formal power series
or a totalized divergent sum.

### Actual rectangular matrix consequence

For arbitrary finite rectangular matrices `A : Matrix m n 𝕜` and
`B : Matrix n m 𝕜`, form

$$
D=\begin{pmatrix}0&A\\B&0\end{pmatrix},\qquad
\Gamma=\begin{pmatrix}I_m&0\\0&-I_n\end{pmatrix}.
$$

Native block multiplication proves anticommutation and
`D² = diag(AB,BA)`. A separate convergent-series argument proves that the
actual exponential preserves these two diagonal blocks. Applying the
continuous matrix trace therefore gives

$$
\boxed{\operatorname{Tr}\exp(tAB)-\operatorname{Tr}\exp(tBA)
=|m|-|n|.}
$$

Both index types may be empty. The constant term accounts for unequal
dimensions. The partners remain arbitrary ordered rectangular matrices:
neither diagonalization nor a commuting scalar replacement appears in the
proof. Taking `B=A*` and a negative real parameter gives the corresponding
finite positive-Hamiltonian heat identity. No unbounded heat-kernel theorem
is asserted.

The historical `SpinorialCore.FiniteSupertrace` already owns the polynomial
trace identity. Its transitive `Algebra.lean` imports the Mathlib umbrella.
The new analytic proof instead reuses the more general cyclic cancellation
owner directly. It introduces no duplicate polynomial API and does not
modify the historical owners or dependency pins.

### The regulator matters even for noncommuting nilpotents

If `E²=0` and `F` is arbitrary, associativity gives

$$
E(EF+FE)=(EF+FE)E.
$$

Native exponential commutation and the existing cyclic commutator theorem
then give

$$
\boxed{\tau\!\left((EF-FE)\exp(t(EF+FE))\right)=0.}
$$

Only the first factor needs to square to zero, and this cancellation theorem
needs an additive cyclic functional, without continuity of that functional.
The commutation proof itself does not require completeness. On the complete
Banach algebras and finite matrix spaces used for the analytic results,
the native exponential has its convergent series.

The source includes an explicit `2×2` noncommuting witness:

$$
E=\begin{pmatrix}0&1\\0&0\end{pmatrix},\qquad
F=\begin{pmatrix}0&0\\1&0\end{pmatrix}.
$$

It proves `E²=F²=0`, `EF≠FE`, vanishing for every exponential parameter above,
and

$$
\operatorname{Tr}\big((EF-FE)(EF)\big)=1.
$$

Thus noncommutation does not force a nonzero naturally regulated trace, and
a nonzero trace against a different weight does not by itself identify a
boundary. This finite witness illustrates the general theorem; it does not
replace its arbitrary-operator proof.

The eight declarations are
`cyclicFunctional_odd_square_positive_power`,
`commute_anticommutator_of_square_zero`,
`cyclicFunctional_exp_odd_square`,
`cyclicFunctional_commutator_exp_anticommutator`,
`exp_fromBlocks_zero_zero`,
`rectangular_exponential_trace_difference`,
`trace_commutator_exp_anticommutator`, and
`noncommuting_nilpotents_distinguish_weights`.

## 4. Claim ledger: what the source does and does not establish

This ledger records mathematical corrections and existing owners separately
from the new source declarations. Elementary examples here are explanatory
calculations unless an explicit Lean owner is named.

| Source motif | Precise disposition |
|---|---|
| Lie-sphere or conformal generators are automatically nilpotent associative operators | Associative nilpotence must be interpreted in a specified representation or associative algebra. For `D=d/dx` on real smooth functions, `D^n exp(x)=exp(x)`, so `D` is not nilpotent. On real or complex polynomials, `D` is locally nilpotent, but no single exponent annihilates the entire polynomial space. Geometric terminology alone supplies none of these operator hypotheses. |
| `X` and `1/X` for a nilpotent | A nonzero nilpotent cannot have an ordinary inverse in a nontrivial unital ring. Moore-Penrose, Drazin, and ordinary inverses differ. Existing `Canonical.MoorePenroseDrazinObstruction` proves the nilpotent MP/Drazin obstruction; `MoorePenroseDrazinCriterion` identifies the additional commutation conditions. |
| Inverse commutation collapses noncommutative algebra | False: an invertible diagonal matrix commutes with its own inverse while failing to commute with an off-diagonal matrix unit. |
| `EFE=E`, `FEF=F` define Moore-Penrose duality | These are only the reflexive inverse equations. Self-adjointness of both support products is also required [S1]. |
| `E₁₄,F₄₁` have full ambient spin squares | Their support unit is `P=P₁₁+P₄₄`. In `M₄`, `(E−F)²=−P`, `(E+F)²=P`, and `[E,F]²=P`; replacing `P` with `I₄` discards the complement. |
| `S²=−I` prevents a projective involution | Scalar matrices act trivially on projective space. The matrix lift can have order four while its projective action has order two. Existing `Canonical.MoebiusClosure.sl2_moebius_inversion_matrix_square` proves the matrix identity; it is not itself a holonomy construction. |
| Zero and infinity are fixed points of `z ↦ −1/z` | They are exchanged. Over the complex numbers the fixed points are `±i`. Exchanging points is different from identifying them. |
| A universal projector defect follows from `S²=−I` | The expression `P²−P=−I/2` follows for the explicit ansatz `P=(I+S)/2`. Without that definition there is no projector claim. Idempotence and involutivity are different equations. |
| Compactification and pinching force a singular non-Hausdorff topology | One-point compactification adds a distinct point [S8]. Appropriate compact Hausdorff quotients can remain Hausdorff; collapsing the equator of a sphere gives a simply connected wedge of spheres. Topological conclusions require the actual quotient and hypotheses. |
| Rota inversion is fractional-linear inversion | Rota's inverse is in an incidence convolution algebra [S7]. In a three-element chain one Möbius coefficient is zero while the zeta function remains invertible. No bridge to the projective action is supplied. |
| Zero Witten index implies no zero modes or broken supersymmetry | False. Equal nonzero kernel counts have zero difference. Existing `Canonical.FiniteSuperchargePairing.paired_zeroSupercharge_index` already allows arbitrarily many paired zero modes. Witten explicitly distinguishes the two possibilities when the index vanishes [S3]. |
| Zero index implies contractibility | A signed count does not establish a contraction. Vanishing reduced Euler characteristic likewise does not suffice; a circle and an isolated point provide a disconnected example. |
| Noncompactness makes a Fredholm index fractional | A Fredholm index remains an integer difference of finite kernel and cokernel dimensions. Loss of Fredholmness changes whether that index is defined. Separately defined regularized non-Fredholm indices may be noninteger under specific analytic hypotheses [S6]. |
| APS gives the universal jump `−eta` | In the APS Dirac setting the formula contains a bulk term and `−(eta(0)+h)/2`, with a spectral boundary condition and geometric hypotheses [S4]. Eta may itself vanish or be noninteger [S5]. The attachment supplies neither the requisite operator nor its limits and boundary problem. |
| KMS strip continuation constructs the missing bounded inverse | No such implication is supplied. The proved bounded inverse here comes from closed range and the existing Hilbert construction. |
| Modular operators are always unbounded or affiliated to the represented algebra | False in general. Finite faithful matrix states give bounded modular operators; their standard Hilbert-Schmidt representative is `Lρ Rρ⁻¹`, generally not a left-multiplication operator. Tracial states give consistent trivial modular flow [S9]. |
| Noninvertibility forces topology, scattering, or a colimit obstruction | A zero matrix is already noninvertible. None of those additional objects is constructed by noninvertibility alone. |
| `K₀ ⊕ B₊ ⊕ C∞` is a canonical Hilbert decomposition | No third summand, projection, or completeness argument is specified. For a closed self-adjoint operator the kernel and closure of the range already give the standard orthogonal split. If `B₊` denotes only point eigenvectors, any missing continuous spectrum need not lie at infinity. |

The new generic trace theorem assumes a continuous cyclic functional on its
chosen Banach algebra. It does not assert an ordinary trace on all bounded
operators of an infinite-dimensional Hilbert space. Moving to such heat
operators requires explicit domains, trace-class ideals, convergence, and
boundary hypotheses. The source's APS, Callias, KMS, and asymptotic-sector
claims remain separate analytic targets, not consequences of the three
new owners.

## 5. Established dependency order

The proof dependencies have two branches:

1. Actual adjoints and native Gram eigenspaces lead to the existing pairing
   and inner-product law, then the normalized isometry. The Penrose equations
   separately give absorption and the eigenspace inverse formula. Combining
   these with the isometry and bounded-operator norm gives the eigenvalue
   bound and the obstruction to closed range.
2. Cyclicity and anticommutation give positive-power cancellation. Continuity
   and the convergent exponential series give the Banach-algebra identity.
   Actual doubled blocks give the rectangular matrix trace formula.
   Square-zero commutation gives the weighted commutator cancellation.

There is no established implication from a projective sign, a vanishing
incidence coefficient, or a finite weighted trace to an APS boundary index,
an asymptotic Hilbert summand, or a KMS-derived pseudoinverse.

## 6. Validation and reproducibility

**Independent QA disposition: ACCEPTED_WITH_LIMITED_SCOPE.** The exact three
owners passed independent mathematical/source review, fresh native
compilation and axiom auditing, strict source gates, and static Gate 4.
The [QA receipt](../artifacts/qms/chiral-reciprocity-20261116/qa-acceptance.json),
[review](../artifacts/qms/chiral-reciprocity-20261116/qa-review.md), and
[complete command ledger](../artifacts/qms/chiral-reciprocity-20261116/command-ledger.json)
record the actual scope and results.

| Owner | Source theorems | Definitions | Native audited declarations |
|---|---:|---:|---:|
| HilbertGramReciprocity | 5 | 1 | 16 |
| HilbertGramMoorePenrose | 7 | 0 | 7 |
| GradedExponentialTrace | 8 | 0 | 10 |
| **Total** | **20** | **1** | **33** |

The accepted source SHA-256 hashes are:

- `HilbertGramReciprocity.lean`:
  `64975ff850e1e32ac98e07a52c2d315e83dcc98a0c60833a854bcbd7d7ddbae9`.
- `HilbertGramMoorePenrose.lean`:
  `aa016bd2a2711ba481373d23496f3e115e84602c0b4321a3e7731ecc219b1f30`.
- `GradedExponentialTrace.lean`:
  `cdde658faa0d10ab862a648062b405c3178eeff0a504bfd0a1be223ccdef3451`.

### Fresh kernel and native declaration audit

The independent QA run rebuilt the exact eight-module repository source
closure against the pinned Mathlib artifacts; no repository module result
was reused. All eight compilations succeeded. The three new owners and the
native audit have zero compiler warnings.

The audit enumerated 33 module-owned declarations, including generated proof
helpers: 16 in HilbertGramReciprocity, 7 in HilbertGramMoorePenrose, and 10 in
GradedExponentialTrace. These counts are distinct from the source inventory
of 20 theorem declarations and one constructed definition. The complete
transitive axiom union was exactly `propext`, `Classical.choice`, and
`Quot.sound`. No additional axiom, proof placeholder, unsafe declaration, or
partial declaration was accepted. The permitted foundations enter through
the native equality/extensionality, noncomputable Hilbert constructions, and
quotient infrastructure; this does not claim every declaration uses each one.

The unchanged `Singular.MoorePenrose` dependency produced 14 warnings:
12 deprecated orthogonal-projection API uses and two `haveI` style suggestions.
Every other dependency had zero warnings. These dependency warnings were
recorded without changing that historical owner or suppressing diagnostics.

The executed fresh command was:

```bash
python3 -B tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/64554963d837/mathlib-4.34.1 \
  --lean /workspace/scratch/64554963d837/lean-runtime/bin/lean \
  --output /workspace/scratch/9eb3301f34a1/reciprocity/final-validation \
  --target InfoGeometry.Analysis.HilbertGramReciprocity \
  --target InfoGeometry.Analysis.HilbertGramMoorePenrose \
  --target InfoGeometry.Analysis.GradedExponentialTrace
```

There was no incremental reuse and no audit skip. Reproduction requires the
same Lean/Mathlib pins and a fresh output directory; the absolute paths above
identify this run's environment.

### Source review and static gates

The three strict placeholder scans passed with zero findings. Semantic-vacuity
coverage was complete for all three owners, with zero errors and one lexical
warning: `normalizedGramEigenspaceEquiv_apply` is proved by `rfl`.
This is the intended forward-action readout of the constructed isometry;
the norm-preservation proof is in the preceding definition. Independent
source review accepted that distinction.

Strict OpenGauss screening and refutation passed with zero current violations.
An initial strict screener run had rejected five scalar automation steps
inside operator owners. Those steps were replaced by explicit native scalar
identities and inequalities. The operator products and theorem hypotheses
were unchanged, the exact revised hashes received an independent A-A delta
review, and QA reran the unchanged strict gates successfully. The failed
attempt and its correction remain recorded in the QA evidence.

Static Gate 4 returned
`STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED` for all three owners: zero proof
placeholders, traps, or scope warnings, with no staged-hook failure or
index-churn caveat. This is deliberately recorded as a static result;
the separate fresh run above supplies the kernel and axiom evidence.
The gate's internally invoked staged-source checks also included the staged
`All.lean` change. They do not constitute compilation of that aggregate.

### Independent review and publication snapshot

Generation was performed by the parent and an isolated Hilbert candidate
author. A separate mathematical/source auditor authored no Lean source.
Independent QA authored neither the accepted theorem content nor its source
audit. Their exact reviews, the correction history, native receipts, and
checksum manifest are preserved in
[the evidence packet](../artifacts/qms/chiral-reciprocity-20261116/README.md).

QA reconciled the frozen worktree and index, all eight compiled source
hashes, 17 unchanged helper/pin files, the clean pinned Mathlib checkout,
and exactly three `All.lean` import additions. The native report records
the base commit because validation used a frozen staged snapshot; its exact
source hashes identify the new owners rather than claiming they already
existed in that base commit.

After QA released the source freeze, this report received only its separately
reviewed display-formatting/source-ledger update and these actual validation
results. The accepted Lean owners, aggregate imports, and theorem contract
were preserved. The separate
[publication integration record](../artifacts/qms/chiral-reciprocity-20261116/publication-integration.json)
records that reconciliation without modifying the original QA receipts.

The actual Git commit hook and committed-range pre-push/post-build checks
belong to the publication phase. Their actual outcomes are recorded in the
pull request body; QA's successful internal staged-gate calls are not
misrepresented as those later invocations.

### Root integration limitation

The independently executed root path-package preflight exited **1**.
`InfoGeometryCore` passed; the following existing dependencies were blocked:

| Dependency | Observed blocker |
|---|---|
| HomotopyHypothesis | Missing directory/configuration at `external_refs/homotopy-hypothesis-lean4`; untracked path-dependency provenance. |
| Atlas | Missing directory/configuration at `external_refs/atlas-lean`; untracked path-dependency provenance. |
| GIFT | Uninitialized gitlink at `e6f3c3ac2140c2324fb2ae029c32233e73aa5e92`, with missing Lake configuration. |

The [preflight receipt](../artifacts/qms/chiral-reciprocity-20261116/root-path-preflight.json)
is a dependency availability/provenance check, not a compilation result.
Neither the three-owner kernel check nor static checking of the aggregate
establishes a successful `InfoGeometry.All` or whole-repository build.
The draft carries this integration limitation explicitly.

The toolchain and dependency pins, gate implementations, historical owner
files, and unrelated sources are unchanged. No placeholder, custom axiom,
unsafe bypass, `native_decide`, or gate suppression was introduced.

## Primary-source register

- **S1. Penrose (1955), _A generalized inverse for matrices_.** Theorem 1 and
  Eq. (8), printed pp. 406-407. [DOI](https://doi.org/10.1017/S0305004100030401).
- **S2. Rakočević and Wei (2001), _The perturbation theory for the Drazin inverse
  and its applications II_.** Definition 1.1.
  [Publisher paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/489535AC7D44547D91AD7254A3531717/S1446788700002597a.pdf/the-perturbation-theory-for-the-drazin-inverse-and-its-applications-ii.pdf).
- **S3. Witten (1982), _Constraints on supersymmetry breaking_.** Positive-energy
  pairing and the explicit zero-index alternatives, printed pp. 254-257.
  [Original paper scan](https://web2.ph.utexas.edu/~vadim/Classes/2025f/Witten1982.pdf).
- **S4. Atiyah, Patodi, Singer (1975), _Spectral asymmetry and Riemannian
  geometry I_.** Eq. (3.9) and Theorem 4.2.
  [Original paper scan](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/aps001.pdf).
- **S5. Atiyah, Patodi, Singer (1973), _Spectral asymmetry and Riemannian
  geometry_.** Circle eta example.
  [Original announcement](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/atiyahspec.pdf).
- **S6. Carey et al. (2015), _On Index Theory for Non-Fredholm Operators:
  A (1+1)-Dimensional Example_.** A specifically defined regularized index.
  [Author preprint](https://arxiv.org/abs/1509.01356).
- **S7. Rota (1964), _On the foundations of combinatorial theory I.
  Theory of Möbius functions_.** Incidence convolution and inversion.
  [Original paper scan](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rota1.pdf).
- **S8. Mathlib, _OnePoint.Basic_.** Injectivity of the inclusion and
  `OnePoint.coe_ne_infty`.
  [Official API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactification/OnePoint/Basic.html).
  Live documentation is conceptual context; compiled APIs use the pinned source.
- **S9. Giorgetti et al. (2021), _Bayesian inversion and the Tomita-Takesaki
  modular group_.** Finite-matrix modular automorphisms.
  [Author preprint](https://arxiv.org/abs/2112.03129).

Sources were retrieved on 2026-11-16. They support the source audit and
mathematical interpretation; Lean acceptance requires the separate
source-closure and axiom checks specified above.
