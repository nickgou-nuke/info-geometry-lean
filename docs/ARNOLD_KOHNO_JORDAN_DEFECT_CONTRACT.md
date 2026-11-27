# Arnold–Kohno, real Jordan flow, and finite defect correction

## Intake and source authority

This work continues the source tree of PR #474 at
`722d33728a967fddec3187bdac1d17a8df758748`. The four supplied texts are
mathematical intake, not evidence that their asserted implications have
already been proved.

| Supplied file | SHA-256 | Role |
|---|---|---|
| `Pasted text(20261127-155020).txt` | `29cbc837d1bde4ebac637d1c7b9769693362252e51f790a8c31af31adff0f5d5` | Prior Arnold/density/contact implementation and explicit integration boundary |
| `Pasted text (2)(20261127-155027).txt` | `c6f6b8312987515cec6de1da45c51bdef71c12fc45864a83f4a90548e68fe335` | Configuration forms, KZ residues, Jordan flow, parabolic and exceptional proposals |
| `Pasted text (3)(10).txt` | `33671afd34a80edc40fa790cbcf394151229ed27e23b87e9efd9b869ac4dbabc` | Repeated narrative synthesis; claims of verification are not build evidence |
| `Pasted text (4)(4).txt` | `893ad55177d609d9460a3cc4bebef491af1103ab1a462b6c22aa7d380ea61355` | Peirce decomposition, nilpotent perturbations, defect iteration, and a proposed finite conceptual order |

The attached source files remain unchanged. Their hashes identify the exact
intake without turning narrative assertions into theorem assumptions.

The implementation uses the repository's pinned Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. No dependency pin is changed.

## 1. Native indexed Arnold–Kohno cancellation

### Existing owners and the missing implication

`Canonical.IndexedArnoldKZComplex` already supplies:

- the injective configuration `Conf n K`;
- `dlogCoefficient` and its nonzero-denominator proof;
- `dlog_partial_fraction`;
- indexed associative `InfinitesimalBraidResidues`.

Its historical `tripleCurvature` specializes the residues to the scalar
field `K`. That specialization makes their commutators zero. It is a valid
scalar statement, but it does not supply the intended operator calculation.

`Canonical.ArnoldKohnoParaKahlerConnection` already proves the genuinely
noncommutative theorem `arnold_kohno_triangle_flat` in a tensor product
\(L\otimes_K\Lambda_K M\), using a native Lie algebra \(L\).

The new owner `Canonical.IndexedArnoldKohnoExterior` connects these two
surfaces through actual degree-one elements in Mathlib's exterior algebra.

### Exact carrier and construction

Let \(K\) be a field, \(M\) a \(K\)-module, and \(L\) an independent
\(K\)-Lie algebra. All constructions specialize to \(K=\mathbb R\).
For an injective configuration \(z:\operatorname{Fin}n\to K\), and chosen
degree-one generators \(dz_i\in M\), define

\[
\alpha_{ij}=(z_i-z_j)^{-1}\iota(dz_i-dz_j)\in\Lambda_K M.
\]

Here \(\iota\) is `ExteriorAlgebra.ι`. These are algebraic exterior
elements; no analytic derivative is encoded by the variable name `dz`.

The new `dlogExterior_arnold` proves

\[
\alpha_{ij}\alpha_{jk}+
\alpha_{jk}\alpha_{ki}+
\alpha_{ki}\alpha_{ij}=0
\]

for pairwise distinct indices. Its proof uses the existing scalar
partial-fraction identity and degree-one exterior anticommutation.
Multiplication on the *entire* exterior algebra is never assumed alternating.

For symmetric residues \(T_{ij}\in L\), the explicit shared-index hypothesis is

\[
[T_{ij},T_{ik}+T_{jk}]=0.
\]

The native tensor theorem then proves

\[
[T_{ij},T_{jk}]\otimes\alpha_{ij}\alpha_{jk}
+[T_{jk},T_{ki}]\otimes\alpha_{jk}\alpha_{ki}
+[T_{ki},T_{ij}]\otimes\alpha_{ki}\alpha_{ij}=0.
\]

The individual residue brackets need not vanish. The family
\(x,y,-(x+y)\) supplies a direct example for arbitrary \(x,y\in L\).
The regression witness uses real upper/lower \(2\times2\) matrix units
whose bracket is nonzero.

The owner also cancels the complete **ordered** finite triangle sum and
the separately defined disjoint-edge sum. The old indexed associative
residue structure is transported to these same tensor expressions by
deriving its shared-index Kohno relations; there is no second residue
structure that simply assumes the desired tensor result.

### Scope boundary

These results prove algebraic quadratic contributions vanish. They do not
yet identify those particular ordered sums, including multiplicities, with
the square of an actual connection one-form. They do not prove an exterior
derivative vanishes, construct parallel transport, or construct a braid
representation. Ordered complex configuration spaces would first give pure
braid monodromy; the unordered quotient requires additional equivariance.

The justified dependency order is:

1. Injective configuration and nonzero differences.
2. Partial fractions and native degree-one exterior identities.
3. Arnold cancellation.
4. Explicit residue symmetry and Kohno relations.
5. Tensor-valued cancellation and finite sums.

Connection calculus and monodromy are later obligations, not consequences
inserted by terminology.

## 2. Real analytic Jordan flow

`Quantum.LogJordanKreinCore` already defines

\[
N=\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
L_\delta=\delta I+N,\quad
G=\begin{pmatrix}0&1\\1&0\end{pmatrix},
\]

and proves \(N^2=0\), \(N\ne0\), and \(L_\delta^T G=G L_\delta\).
Its `expJordanCell t delta` is defined by a closed expression.
The separate canonical Jordan owner already has a specialized native
exponential formula; this extension is not described as the first such
theorem in the repository.

`Quantum.RealJordanFlow` supplies a reusable theorem for every finite
real square-zero matrix:

\[
A^2=0\quad\Longrightarrow\quad \exp(tA)=I+tA.
\]

The left side is Mathlib's analytic `NormedSpace.exp`. The proof reduces
its series and shows that every term of order at least two vanishes.
Scalar matrices commute with \(A\), so

\[
\exp(sI+tA)=e^s(I+tA).
\]

This identifies the quantum owner's existing expression with
\(\exp(tL_\delta)\). The resulting evolution has:

- the additive parameter law \(E(s+t)=E(s)E(t)\);
- both inverse identities \(E(t)E(-t)=E(-t)E(t)=I\);
- a native homomorphism `Multiplicative ℝ →* M2Rˣ`.

The homomorphism is an algebraic one-parameter group. Its continuity is
not bundled or separately proved by this owner.

For \(x>0\), the positive real reparameterization \(t=\log x\) gives

\[
\exp((\log x)L_\delta)=
x^\delta(I+(\log x)N).
\]

The existing readouts now apply to the actual exponential:

\[
\operatorname{tr}\exp((\log x)L_\delta)=2x^\delta,\qquad
\operatorname{tr}(N^T\exp((\log x)L_\delta))
=(\log x)x^\delta.
\]

The detector coefficient vanishes exactly when \(x=1\). This is a real
logarithmic parameter identity; it is not a branch-cut or monodromy theorem.

### Positive inner product versus Krein symmetry

The same owner proves that an everywhere-defined real symmetric linear map
\(T\) on a positive inner product space with \(T^2=0\) is zero:

\[
\langle Tv,Tv\rangle=\langle v,T^2v\rangle=0.
\]

Neither finite dimensionality nor completeness is needed. It also proves
the scalar-shift consequence: symmetric \(T\) with
\((T-\delta I)^2=0\) satisfies \(T=\delta I\).

The nonzero real Jordan shear is therefore an example of the existing
indefinite symmetry, not a positive-Hilbert symmetric nilpotent.
The result does not address domain questions for unbounded operators.
The new carriers are real; existing transitive imports may also contain
complex declarations.

## 3. Finite correction of a nilpotent idempotency defect

The defect is \(\delta(x)=x^2-x\). The existing
`Core.IdempotentDefectIteration` owns

\[
f(x)=3x^2-2x^3,\qquad
\delta(f(x))=\delta(x)^2(4\delta(x)-3).
\]

These are arbitrary associative-ring identities; no commutative ambient
ring or division is assumed.

The new focused owner `Core.NewtonIdempotentCorrection` extracts the
existing finite-orbit proofs from
`OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry`. Thirteen
original public theorem names remain available through compatibility
aliases. The base defect and correction definitions are unchanged.
The extracted factorization is

\[
\delta(f^n(x))=\delta(x)^{2^n}R_n,\qquad
[\delta(x),R_n]=0.
\]

The new extension proves:

- every correction iterate belongs to every subring containing \(x\);
- hence the entire orbit stays in \(\operatorname{Subring.closure}\{x\}\);
- if \(\delta(x)^m=0\) and \(m\le2^n\), the actual iterate \(f^n(x)\)
  is idempotent;
- if the initial defect is nilpotent, some actual iterate is idempotent,
  commutes with \(x\), belongs to the generated subring, and is fixed by
  every later step.

The final existence statement explicitly identifies an element of the
Newton orbit. It does not merely assert existence of a commuting idempotent,
which would be trivially witnessed by zero.

The proved sufficient bound is \(m\le2^n\). No least stopping-time
theorem or termination for arbitrary nonnilpotent defects is asserted.
This cubic correction is distinct from repeatedly applying \(\delta\)
itself.

## 4. Corrections and remaining obligations

| Intake implication | Source-grounded disposition |
|---|---|
| Nonzero square-zero perturbation always destroys idempotence | False: for \(P^2=P\), \(N^2=0\), idempotence of \(P+N\) is exactly \(PN+NP=N\). Existing Peirce corner theorems supply examples. |
| Defect polarization is the commutator | False: \(\delta(x+y)-\delta(x)-\delta(y)=xy+yx\), the anticommutator. |
| Nilpotent motion is algebraically irreversible | False for square-zero shear: \((I+tN)^{-1}=I-tN\). |
| Noncommuting braid operators must have Jordan blocks | Not implied. Nonsemisimplicity requires separate representation hypotheses. |
| A Levi decomposition supplies commuting Jordan–Chevalley factors | Not in general. The Levi factor and the radical need not commute. |
| A finite conceptual order proves an infinite strictly ascending algebraic tower | Not implied. Explicit objects, actions, extension maps, and limit laws are missing. |
| Nilpotent defect forces endless correction | False for this cubic correction: the new theorem gives finite stabilization. |
| A Heisenberg symbol alone determines the finite exceptional \(E_8\) prolongation | Additional degree-zero structure and invariant data are required; no exceptional classification is claimed here. |
| Arnold/density geometry, KZ monodromy, and modular dynamics are one already-constructed object | Explicit comparison maps remain required. The current owners certify separate stated structures. |

The twelve-node conceptual diagram in the fourth attachment is intake
organization. It is not used as a substitute for Lean declaration
dependencies or as evidence of an infinite tower.

## Primary mathematical references

- Khesin, Misiołek, Modin, *Information geometry of diffeomorphism groups*,
  [arXiv:2411.03265](https://arxiv.org/html/2411.03265v1).
- Kohno, *Local systems on configuration spaces, KZ connections and conformal
  blocks*, especially Section 5,
  [author's PDF](https://www.ms.u-tokyo.ac.jp/~kohno/papers/kohno_config.pdf).
- The Stacks Project, [Lemma 10.32.6, tag 00J9](https://stacks.math.columbia.edu/tag/00J9),
  second proof, for the classical cubic idempotent correction. That source is
  in commutative algebra; the repository's ordered polynomial identities are
  checked over an arbitrary associative ring. Its commutative uniqueness
  conclusion is not imported into the noncommutative theorem.

## Validation record

### Final selected-source compiler result

The final fresh run passes with Lean 4.34.1 at compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52` and the pinned Mathlib revision.
It compiles all eighteen modules in the selected source closure and audits
all 186 declarations owned by the eight selected modules, including
generated declarations. The eight owners compile with warnings treated as
errors. There are zero unsafe declarations, zero partial declarations,
and zero unapproved transitive axiom dependencies in that owned set.

| Selected owner | Audited declarations |
|---|---:|
| `InfoGeometry.Canonical.KZResidueBracket` | 1 |
| `InfoGeometry.Canonical.ArnoldCohenBCFWBridge` | 51 |
| `InfoGeometry.Canonical.IndexedArnoldKZComplex` | 37 |
| `InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection` | 26 |
| `InfoGeometry.Canonical.IndexedArnoldKohnoExterior` | 21 |
| `InfoGeometry.Canonical.IndexedArnoldKohnoExamples` | 6 |
| `InfoGeometry.Quantum.RealJordanFlow` | 22 |
| `InfoGeometry.Core.NewtonIdempotentCorrection` | 22 |
| **Total** | **186** |

The declaration kinds are 115 theorems, 59 definitions, four inductives,
four constructors, and four recursors. These are audit totals, not a count
of newly proved theorems: existing owners and generated declarations are
included.

There is one inherited dependency warning in
`Core/PeirceDecomposition.lean:192` (`linter.unnecessarySeqFocus`). It is
outside the selected warning-as-error owners and is not counted as an
owner warning or a proof gap.

The final run has these recorded artifact hashes:

- [Selected-source result](verification/ArnoldKohnoJordanDefect/selected-source-result.json): `148c3f6467092f086eb79099187488f80784721d3f2f52d12edd0833a7283fb1`.
- [Native declaration audit](verification/ArnoldKohnoJordanDefect/declaration-audit.jsonl): `44dc15cbc23eabc94d6257ede51112ca4790a74f2a72bc95eecbff89db8220ef`.

These are byte-for-byte copies of the successful run outputs. Absolute paths
inside them identify that verification workspace. Their repository-head field
records the pre-commit base; the source hashes identify the actual checked
edited files. The declaration records expose the native type/proof
dependencies and the dependencies among the audited owners.

The earlier fresh independent run checked the same other seventeen source
files. The final run additionally checks the extracted closed
`real_matrix_noncommutative` witness and its use by the triangle theorem.
KZ/Jordan and Newton mathematics received separate cross-reviews; compiler
verification is reported independently from those source reviews.

### Historical Peirce compatibility

A separate fresh supplemental run compiles the historical
`OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry` owner and its
complete forty-nine-module local source closure. The modified facade and
the thirteen-alias audit both pass with warnings treated as errors.
All thirteen aliases retain their original theorem signatures and depend
transitively only on the three permitted foundational axioms.

The run validates the same Lean binary, Mathlib revision, eight dependency
pins, source hashes, and shared build lock. Forty-seven of its sources match
the base commit exactly; the remaining sources are the new focused Newton
owner and the modified historical facade. No retained baseline artifacts
are reused. There are twenty existing warnings in eight unchanged dependency
files; the changed facade has no warnings.

The maintained closure collector currently misreads the words `import graph.`
inside a block comment in `Meta.EpistemicCompilerChain` as an import. The
supplemental discovery step removes comments for dependency discovery only;
it compiles the original source bytes without rewriting them. The maintained
checker is unchanged. This result is explicitly supplemental compilation
and a thirteen-theorem axiom audit, not an all-declaration audit of those
forty-nine modules or a replacement for the root gate.

- [Supplemental result](verification/ArnoldKohnoJordanDefect/peirce-compatibility-result.json): `5ab51c68eb66669fd4e591059d78043f14993868194f4159bcde25c6705aaae8`.
- [Native alias audit](verification/ArnoldKohnoJordanDefect/peirce-alias-audit.log): `f7cc2e680d9ba2a352a5e64ae6a56dcefd600fc8d29773cc6343cfe28115d05f`.

### Historical KZ boundary

The historical `KZLogarithmicConnection` executable text is unchanged after
removing comments, import directives, and the bracket declaration moved
verbatim to `KZResidueBracket`. Its names, namespace, and mathematical
statements are preserved by source review. Its full historical consumer
closure is not compiled by these checks: it has 229 local modules and
additional `Architect` imports outside the selected proof lane. No whole
legacy-KZ compilation certificate is claimed.

### Reproduction

From the repository root, provide the exact pinned Mathlib checkout and
Lean binary to the maintained source-snapshot checker:

```bash
python3 tools/quality/check_operator_geometry.py \
  --repo "$PWD" \
  --mathlib /path/to/pinned/mathlib \
  --lean /path/to/lean-4.34.1/bin/lean \
  --work-dir /path/to/fresh/check-output \
  --owner InfoGeometry.Canonical.KZResidueBracket \
  --owner InfoGeometry.Canonical.ArnoldCohenBCFWBridge \
  --owner InfoGeometry.Canonical.IndexedArnoldKZComplex \
  --owner InfoGeometry.Canonical.ArnoldKohnoParaKahlerConnection \
  --owner InfoGeometry.Canonical.IndexedArnoldKohnoExterior \
  --owner InfoGeometry.Canonical.IndexedArnoldKohnoExamples \
  --owner InfoGeometry.Quantum.RealJordanFlow \
  --owner InfoGeometry.Core.NewtonIdempotentCorrection \
  --target InfoGeometry.Canonical.ArnoldKohnoJordanDefect \
  --owner-warnings-as-errors \
  --audit \
  --audit-source tools/quality/ArnoldKohnoJordanDeclarationAudit.lean
```

The checker validates the compiler and dependency pins, copies the actual
selected source closure, records source hashes, compiles under the shared
build lock, and audits every declaration owned by the eight selected
modules. The audit includes generated declarations and follows axiom
use transitively. It accepts only `propext`, `Classical.choice`, and
`Quot.sound`; it rejects unsafe or partial owned declarations and local
axiom declarations.

### Source and gate checks

The staged proof-integrity gate, changed-source debt audit, semantic-content
audit, and source-scope audit pass. The source-debt scan covers fourteen
changed Lean files and reports zero `sorry`, `admit`, or `axiom` gaps.
The semantic-content scan covers the thirteen changed files in `lean/`
and reports zero blocking or review findings.

The separate heuristic semantic-vacuity scan passes its error threshold
with eleven warnings. These flag existing structure-law fields and short
identity/contribution lemmas, including `dlogExterior_self`,
`disjointContribution_eq_zero`, and `expJordanCell_zero`. They are not
silently counted as a warning-free scan. Cross-review checked the new
owners' actual hypotheses and conclusions, including the noncommuting
matrix witness and the specific Newton orbit in the stabilization theorem.

The post-build gate now routes the new declaration-audit source through
its existing locked standalone Lean check. Only the two exact basename
routing lists were extended. Shell syntax validation and positive/negative
routing checks pass; unlisted lookalike paths remain rejected. The
compiler, snapshot checker, axiom whitelist, and proof-integrity rules
are unchanged.

### Root-package integration boundary

The root dependency preflight fails for these recorded path dependencies:

| Package | Recorded path | Observed issue |
|---|---|---|
| `HomotopyHypothesis` | `external_refs/homotopy-hypothesis-lean4` | Missing configuration; untracked path dependency |
| `Atlas` | `external_refs/atlas-lean` | Missing configuration; untracked path dependency |
| `GIFT` | `external_refs/gift-framework-core` | Uninitialized gitlink; missing configuration |

The recorded GIFT gitlink is
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92`. The other two missing package
sources cannot be reconstructed from a recorded gitlink in this checkout.
No stub package or alternate upstream revision substitutes for them.

Reproduce the preflight and root build with:

```bash
python3 tools/infra/ci_bootstrap.py paths --report /path/to/path-preflight.json
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.All
```

The scoped compiler result does not certify `InfoGeometry.All` or the
entire repository. The two umbrella import additions require the root
build once its dependencies are restored. Likewise, mathematical source
review of preserved legacy declaration signatures is distinct from a
compiler check of every legacy consumer.

### Committed source binding before publication

The mathematical implementation is committed as
`1c07ea22c155cb624d6708ed14d445d8bfa8483b` on
`codex/arnold-kz-jordan-defect-20261127`. Its pre-commit proof-integrity gate
passes. Every source hash in both successful compiler records matches the
corresponding committed Git blob: eighteen selected-closure records and
forty-nine compatibility records, covering fifty-eight distinct Lean files.

The final [root path preflight](verification/ArnoldKohnoJordanDefect/root-path-preflight.json)
returns exit 1 with the three missing dependency configurations listed above.
The [nonwaiting root build invocation](verification/ArnoldKohnoJordanDefect/root-build-lock-boundary.log)
returns exit 2 because another compiler job holds the required shared lock;
it refuses concurrent compilation. The queued waiting invocation was stopped
before it acquired that lock. Thus no successful root compilation or complete
post-build/pre-push gate is claimed.

At this prepublication checkpoint no GitHub branch update, pull-request
creation, or merge had been performed for this extension. The subsequent
draft publication is recorded below. Restoring the recorded path-dependency
sources and completing the normal root gate remain outstanding; the scoped
proof certificates do not certify that gate.

### Upstream draft publication — 2026-11-27

[Draft PR #476](https://github.com/nickgou-nuke/info-geometry-lean/pull/476)
publishes this extension in `nickgou-nuke/info-geometry-lean` from
`codex/arnold-kz-jordan-defect-20261127`. It is stacked on
[PR #474](https://github.com/nickgou-nuke/info-geometry-lean/pull/474), targeting
`codex/arnold-beltrami-cotangent-flow-20261127` at
`722d33728a967fddec3187bdac1d17a8df758748`. The initial review diff contains
the extension's twenty-two changed files.

The initial published commit is
`7912464ec7142ef4347bd6b281eecae024b57546`. Its Git tree
`1c49f48a6ee26cdbe14e5bffb3df218ff61849a3` exactly matches local verification-bound
snapshot `ad1ddc3fdc3095733c69c5f315d530404f6ecebb`. The GitHub-created commit
has different commit metadata; its source tree is identical. This receipt
is a subsequent documentation-only change, with all checked Lean source
hashes preserved.

The draft publication follows the user's explicit request after the scoped
verification results and root integration limits were reported. During
publication the actual `.githooks/pre-push` invocation against the verified
local snapshot reached the locked incremental root build and waited for the
shared compiler lock. It was stopped before acquiring that lock. A fresh
root path preflight again returned exit 1 for the same three unavailable
dependency configurations listed above.

The PR is published for review as a draft. No merge, successful root build,
or completed post-build/pre-push gate is claimed. The missing dependency
sources and full root validation remain integration requirements.
