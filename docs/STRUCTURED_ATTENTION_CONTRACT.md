# Structured operators, causal support, and Krein transport

## Intake and scope

This task compiles the three unedited user attachments preserved in
[`intake/structured-attention-2026-11-04`](intake/structured-attention-2026-11-04/provenance.json).
The manifest records their original filenames, byte counts, SHA-256 hashes,
and base revision `3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`.
The archived assertions and printed `PASS` strings are input, not evidence.

The intended output is ordinary Lean 4 mathematics over native Mathlib
carriers. Psychological and alchemical names organize the intake only; they
are not premises from which an operator identity follows. A dependency arrow
means an actual use of a proved lemma. No universal physical synthesis is
assumed.

## Ground-truth contracts recorded before implementation

1. **Ordered local algebra.** On `Matrix I I A`, with arbitrary finite `I`,
   noncommutative coefficient ring `A`, and an involutive permutation `s`,
   put `X = s.toPEquiv.toMatrix`, `D(a) = Matrix.diagonal a`. The actual
   matrix product of `D(a) + X * D(b)` and `D(c) + X * D(d)` has right
   coefficients `a*c + (b ∘ s)*d` and `(a ∘ s)*d + b*c`.
   Function multiplication is pointwise and the order of values in `A`
   remains fixed. Derive the exact idempotency defect and closure of its
   finite iterates. No claim of universal dense factorization follows.
2. **Two-stage Monarch operator.** On `Matrix (C × F) (C × F) A`, use actual
   block-diagonal matrices and coordinate swapping, with arbitrary finite
   index types. Establish the entry `L f c d * R d f g` by multiplying those
   matrices. Over commutative coefficients, fixing `f,d` makes the slice in
   `c,g` have zero two-by-two minors. Ordinary coarse blocks need not have
   rank one. Exhibit a four-dimensional member whose square and actual
   idempotency defect cannot have this factorization; do not claim that
   every square or defect leaves the class.
3. **Adjoint and causal support.** Reuse native symmetry and triangular
   predicates. Symmetry together with lower-triangular support forces a
   diagonal matrix. A nonzero skew part alone is not causal support.
   Fixed involution conjugation transports products and commutators;
   commutativity follows only when the input coefficients commute.
4. **Cayley form transport.** Extend the existing
   `OperatorAlgebra.NoncommutativeCayleyPair.cayley x r = (1-x)*r` owner.
   In an arbitrary starred ring, derive its exact form defect under
   `(1+x)*r=1`, then form preservation under `star x * J + J*x=0`.
   Keep the resolvent assumption explicit. Preservation of `J` is not a
   positive norm bound. Ordered products have an exact transported defect.
5. **Depth countermodel.** On an arbitrary real module `E`, construct the
   actual endomorphism `T = (5/4) I + (3/4) swap` of `E × E`. For every
   bilinear form `B`, its powers preserve `B ⊕ -B`, while
   `T^n(v,v) = 2^n • (v,v)`. When `E` is a real normed space, in the native
   product sup norm its nonzero diagonal orbits exceed every proposed real
   bound. This is not an operator-norm or
   gradient theorem, and it does not identify the product sup norm with a
   Hilbert direct-sum norm.

## Reused owners and smallest gaps

| Owner | Actual scope | Task use or missing implication |
|---|---|---|
| `Core.IdempotencyDefect` | `x*x-x` in an arbitrary associative ring; polarization | Reuse the definition for local closure; no convergence conclusion |
| Mathlib `Data.Matrix.PEquiv` | Matrix of a partial equivalence; row/column reindexing | Reuse the permutation convention `X*v = v ∘ s`; prove the diagonal crossing law |
| Mathlib `Data.Matrix.Block` | Actual block-diagonal matrices | Derive the two-stage product and its correctly indexed minor |
| Mathlib `LinearAlgebra.Matrix.Block`, `Symmetric`, `IsDiag` | Native support, symmetry, and diagonality | Prove their implication without inventing a causality predicate |
| `OperatorAlgebra.NoncommutativeCayleyPair` | Noncommutative explicit-resolvent Cayley identities | Add starred form transport and composition defect |
| `Canonical.SpinorialCore.KreinAdjoint` | `IsIsometry J U := star U*J*U=J`; product closure | Align the new raw equality with this existing predicate; do not redefine it |
| `Core.HyperbolicPeirceRotor` | Algebraic rotor composition and inverses on a dual-seed carrier | Existing finite algebra does not establish uniform bounds with depth |
| `Canonical.OperatorContentNetwork.CausalBlocks` | Relation-supported real block matrices and a support subalgebra | Its convention `i ≤ j` is upper support; distinguish autoregressive lower support |

Owner discovery combined filename, declaration, alternate-formulation,
import, and consumer searches in the current checkout. The bounded searches
found specialized permutation/diagonal identities and finite Clifford owners,
but no generic two-stage Monarch minor theorem. They do not certify absence
from every historical or unavailable external source.

## Claim ledger

| Intake claim | Disposition before validation | Exact correction or boundary |
|---|---|---|
| Any dense matrix has a fixed logarithmic-stage exact butterfly representation | Counterclaim required | Sparse-factor families do not automatically equal the entire matrix algebra |
| Bare XOR permutations span all off-diagonal matrices | False in general | Diagonal coefficient functions are needed; a bare permutation span is much smaller |
| Diagonal averaging is a grading involution | False terminology | The averaging map is a projection, not generally an involution |
| Single-scale multiplication preserves its normal form | Provable | Use crossed, ordered coefficients, not a commuting surrogate |
| Every fixed coarse Monarch block has rank at most one | False | Fix output fine and input coarse indices instead |
| Every Monarch square lies outside Monarch | False | Prove an existential nonclosure witness; identity is an immediate exception |
| Cyclic shift cannot be a butterfly | False for the stated stages | High-to-low controlled bit flips followed by the low bit implement increment |
| Walsh-conjugated diagonal operators commute | Conditional | True for scalar diagonal coefficients; operator-valued entries retain their commutators |
| A nonzero skew part establishes autoregressive causality | False | Causality requires a specified dependency/support condition |
| `[S+K,(S+K)ᵀ]=2[S,K]` for symmetric `S`, skew `K` | Wrong sign | The sign is negative |
| The supplied Pauli and Witt programs agree | False | With `epsilon=XZ`, the two off-diagonal Witt coefficients are reversed |
| Supplied code ran all advertised checks | Unsupported and contradicted | File 2 contains `A_diag_ conjugated`, which is not a Python identifier |
| File 3 polar and causal coefficients are bit invariant | False | They are anti-invariant: the actual local block collapses to `(a+b)I+(c-d)X`, which is symmetric |
| The normalized boost is the stated Cayley transform at `kappa*X` | False parameter identification | It has rapidity `atanh(kappa)`; that Cayley chart has a different parameter law |
| Krein conservation plus a bounded per-layer parameter controls arbitrary depth | False | Repeated boosts can amplify a null direction geometrically |
| XOR swizzling makes every GPU access conflict free | Unsupported generalization | The supplied check concerns only rows and columns in a particular bank-address model |
| Two Monarch passes saturate a universal I/O bound | Open/unsupported | Requires a specified computation model, parameter traffic, and implementation |
| The supplied cascade refactors softmax attention exactly | False for the supplied program | With `Q=K=0` the gates vanish, while ordinary softmax attention preserves constant nonzero `V` |

## From the requested relational vocabulary to typed mathematics

The existing Peirce owners supply the binary cut and four components. For
an idempotent `p` in an associative ring, set `q = 1-p`. The proved
relations are `p+q=1`, `p*q=q*p=0`, and

\[
A=pAp+pAq+qAp+qAq.
\]

| Relational role in the intake | Precise operator expression | Existing owner |
|---|---|---|
| Internal self-action | `p*A*p` | `Core.PeirceDecomposition.component11` |
| Action from the complementary sector into the selected sector | `p*A*q` | `component10` |
| Action from the selected sector into the complement | `q*A*p` | `component01` |
| Autonomous complementary action | `q*A*q` | `component00` |

This is a mathematical interpretation of the supplied vocabulary, not a
theorem about consciousness. Under the column-vector convention, `p*A*q`
acts from the `q` sector to the `p` sector. Reversing that interpretation
would reverse the meaning of the directed corners.

For `u` in `pAq` and `v` in `qAp`, chosen independently (with no linear
independence hypothesis), the existing
`Core.PeirceCoupledCorners` and `Core.PeirceQuadraticFrame` owners prove the
noncommutative relations

\[
Q=uv+vu,\quad C=uv-vu,\quad X=u+v,\quad Y=u-v,
\]
\[
X^2=Q,\qquad Y^2=-Q,\qquad YX=C,\qquad XY=-C,\qquad C^2=Q^2.
\]

The two round trips `uv` and `vu` occupy different sectors. Their sum and
difference do not identify the directions. The task reuses these owners;
it does not duplicate them under psychological names. The axiom companion
also checks the selected reused Peirce and defect declarations.

Two distinct defects occur in the new work:

\[
\delta(A)=A^2-A,\qquad \mathcal E_J(U)=U^*JU-J.
\]

The first detects idempotence. The second detects preservation of a specified
form. Neither is identified with the other, with a physical phase transition,
or with a norm estimate.

## Implemented proof chains

### Ordered local algebra and the defect tower

[`InvolutiveDiagonalAlgebra.lean`](../lean/InfoGeometry/Routing/InvolutiveDiagonalAlgebra.lean)
has 10 theorems and two constructions. For `s²=id`, write
`tau(a)=a ∘ s` and `B(a,b)=D(a)+X*D(b)`. The exact law is

\[
B(a,b)B(c,d)=B\bigl(ac+\tau(b)d,\;\tau(a)d+bc\bigr).
\]

Consequently,

\[
\delta(B(a,b))=
B\bigl(a^2+\tau(b)b-a,\;\tau(a)b+ba-b\bigr).
\]

`localSubalgebra` proves the closure obligations for a native Mathlib
subalgebra; `iterate_defect_local` then invokes the existing generic
`DefectIteration.iterate_mem_subalgebra`. The recursive tower is indexed by
`Nat`. It is not a convergence argument. The coefficient ring may itself be
a noncommutative matrix or endomorphism ring. No uniqueness of `(a,b)` is
claimed when `s` has fixed points.

### Two-stage geometry and the obstruction

[`MonarchFactorization.lean`](../lean/InfoGeometry/OperatorAlgebra/MonarchFactorization.lean)
has 12 theorems and three constructions. `monarch` is the actual product of
native block-diagonal matrices with one coordinate swap. Its entry law is

\[
M_{(c,f),(d,g)}=L_f(c,d)R_d(f,g).
\]

Reversing the stages gives `R_c(f,g)L_g(c,d)`, changing both coefficient
order and sampled indices. Over a commutative ring, fixing `f,d` gives

\[
M_{(c_0,f),(d,g_0)}M_{(c_1,f),(d,g_1)}
-M_{(c_0,f),(d,g_1)}M_{(c_1,f),(d,g_0)}=0.
\]

The proof only calls this a vanishing minor, so it does not need a field or
a separate rank definition. The four-dimensional controlled-switch witness
has a square with the relevant minor `1`, and a defect with another minor
`-1`. `Nontrivial A` excludes the zero ring when deriving nonfactorization.
The same file proves that identity stages give identity and that an ordinary
coarse block of that identity has minor `1`.

### Filter commutativity and causal support

[`SymmetricCausalBoundary.lean`](../lean/InfoGeometry/Routing/SymmetricCausalBoundary.lean)
has seven theorems. The native action of units proves

\[
[HD(a)H,HD(b)H]=HD(ab-ba)H\quad(H^2=1).
\]

Scalar diagonal filters commute; operator-valued diagonal coefficients need
not. The module constructs no Walsh matrix and verifies no FWHT operation
count. Its filter results are conditional on the supplied involution.

For any linearly ordered index type, native `Matrix.IsSymm` and
`Matrix.IsLowerTriangular` imply `Matrix.IsDiag`. This is a linear support
theorem. For an input-dependent layer `A(X)`, the dependency of the entries
on future inputs must also be checked. The independent starred-ring theorem
proves the corrected sign

\[
[S+K,(S+K)^*]=-2[S,K]
\quad(S^*=S,\ K^*=-K).
\]

### Cayley transport and positive-norm growth

[`CayleyFormTransport.lean`](../lean/InfoGeometry/Krein/CayleyFormTransport.lean)
has eight theorems and introduces no competing transform or metric
predicate. It uses the existing expression `cayley x r=(1-x)*r` and proves

\[
\mathcal E_J(UV)=V^*\mathcal E_J(U)V+\mathcal E_J(V),
\]
\[
\mathcal E_J((1-x)r)=-2r^*(x^*J+Jx)r
\quad\text{if }(1+x)r=1.
\]

It derives preservation under the infinitesimal skewness equation and gives
both a finite-power defect sum and preservation for an ordered list of
different layers. Native `List.prod [U1,U2,...]` means `U1*U2*...`; on column
vectors the rightmost factor acts first. The equality is the existing Krein
`IsIsometry` predicate unfolded, but this lightweight owner does not import
that predicate or add a separate adapter.

[`HyperbolicDepth.lean`](../lean/InfoGeometry/Krein/HyperbolicDepth.lean)
has 12 theorems and three constructions. It acts on the whole product module,
not on a scalar replacement for that module:

\[
T_{c,s}(x,y)=(cx+sy,sx+cy),\qquad
\mathcal B((x,y),(z,w))=B(x,z)-B(y,w).
\]

The transport formula is
\(\mathcal B(Tu,Tv)=(c^2-s^2)\mathcal B(u,v)\). At `c=5/4,s=3/4`, every power
preserves the form, yet

\[
T^n(v,v)=2^n(v,v),\qquad
\|T^n(v,v)\|_{\mathrm{prod}}=2^n\|v\|.
\]

The final theorem proves `forall C, exists n, C < norm (T^n (v,v))` for
nonzero `v`. Thus an actual fixed form-preserving operator disproves a
uniform bound inferred only from indefinite conservation. The native norm
here is the product sup norm; no Hilbert-product, operator-norm, Jacobian,
floating-point, or gradient result is attached to it.

## Dependency poset and synthesis

The table records proof dependencies, not metaphorical equivalences. Each
row uses declarations or constructions earlier in its own branch. The local
algebra and Monarch branches use the same idempotency-defect definition;
the Cayley branch has its separate form discrepancy. No unproved map
identifies the distinct carriers or these different defects.

| Node | Direct proof inputs | Result |
|---|---|---|
| L1 | Native diagonal and permutation matrices | Crossing and conjugation identities |
| L2 | L1, actual matrix multiplication | `localOperator_mul` and exact `defect_localOperator` |
| L3 | L2, proved subalgebra closure, generic defect iteration | Every finite defect iterate remains local |
| M1 | Native block diagonals, swapping, matrix multiplication | Ordered and reversed stage entry laws |
| M2 | M1 and commutative coefficient multiplication | Correct reshuffled minors vanish |
| M3 | M2 and explicit switch square/defect calculations | Square and defect nonfactorization |
| S1 | Native unit-conjugation action | Ordered diagonal product and commutator transport |
| S2 | Native symmetry and triangular support | A symmetric lower-triangular matrix is diagonal |
| K1 | Star reversal and associative multiplication | Ordered product discrepancy |
| K2 | Polynomial factor discrepancy and right-resolvent equation | Exact Cayley discrepancy and preservation |
| K3a | K1, induction on powers | Exact finite-power defect sum |
| K3b | K1, individual preservation hypotheses, list induction | An ordered list of different layers preserves the form |
| K3c | K2 and K3a | Every finite power of the admissible Cayley transform preserves the form |
| H1 | Product projections, native swap, bilinearity | Whole split-form scaling and preservation |
| H2 | Native boost action and endomorphism powers | Exact diagonal action at finite depth |
| H3 | H2 and native positive norm scaling | Exact norm of the diagonal orbit |
| H4 | H3 and the Archimedean power theorem | Every finite proposed norm bound is exceeded |

The structural conclusion is the conjunction of these specific results:
local one-permutation operators form a defect-closed subalgebra; a two-stage
Monarch family has a different closure behavior; a fixed basis change retains
coefficient commutators; causal support and adjoint symmetry are separate
conditions; and split-form conservation permits unbounded positive-norm
orbits. A single total chain of universal philosophical necessities would
require additional implications that these results do not supply.

## External source checks and residual claims

The original Monarch paper, Section 3.3, Equation (2), Algorithm 1, and
Appendix D.2, fixes the middle two indices of its four-index tensor when
forming rank-one slices. This agrees with the corrected entry/minor contract:
[Dao et al., *Monarch*](https://arxiv.org/pdf/2204.00595).

The original butterfly paper, Proposition 1, distinguishes low-depth
representations of particular fast transforms from an inclusion of arbitrary
matrices at depth growing linearly with dimension. It does not establish the
intake's fixed logarithmic-depth universal dense refactoring:
[Dao et al., *Learning Fast Algorithms for Linear Transforms Using Butterfly Factorizations*](https://proceedings.mlr.press/v97/dao19a/dao19a.pdf).

The source code's local parity collapse follows directly from
`diag(b,-b)*Z=bI` and `diag(d,-d)*(XZ)=-dX`. Its syntax error and reversed
Witt coefficients are source-inspection findings. They are not results of
running the supplied programs. No PyTorch or GPU execution is claimed.
[PyTorch's `torch.flip` documentation](https://docs.pytorch.org/docs/2.15/generated/torch.flip.html)
also describes a data copy; these tensor expressions do not certify a
register-only CUDA implementation.

The following remain outside the promoted theorem set: an implementation
and cost theorem for FWHT; a universal butterfly or Kaleidoscope expressivity
classification; equivalence with softmax attention; autoregressive masking of
input-dependent coefficients; a GPU bank/transaction model and measured
kernel performance; a Hong-Kung optimality proof; a Cayley identity-component
theorem; and positive-norm or gradient control for a trained network.

## Validation record

Validation date: **2026-11-04**. Base: upstream `main` at
`3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`. Pins remain Lean **4.34.1** and
Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**.

Generation, read-only mathematical review, and final QA were performed by
separate roles. The independent reviewer accepted the exact mathematical
scope and the corrected contract. Independent QA then rebuilt all **16
repository-owned modules** in the audit companion's import closure, including
the five new owners and the companion. All 16 exited **0**, with no compiler
warnings or errors. Every closure-source hash and all six staged-source
hashes remained unchanged during QA.

The staged proof screener subsequently flagged two scalar `ring` calls
after matrix-entry or bilinear-form projection. Their proofs were refined
to expose coefficient commutation explicitly: `ac_rfl` in the declared
commutative coefficient ring for the Monarch minor, and `mul_comm s c`
followed by additive normalization over the real numbers for split-form
transport. No statement or hypothesis changed. A separate read-only
mathematical review accepted those two refinements.

Independent delta QA then rebuilt both revised owners and the complete
axiom companion, all with exit **0**, and verified that the other **14**
closure-source hashes and all **13** reused dependency-artifact hashes
matched the original QA. All six staged-source hashes matched the final
worktree before and after the check. The 67 axiom reports, exact-six text
scan, maintained debt audit, and maintained staged proof gate passed again.
The delta compiler run had no errors and one advisory warning: the
`add_mul` simplification argument in `HyperbolicDepth` is unused.

| Check | Observed result | Scope |
|---|---|---|
| Locked Lean compilation in the isolated pinned Mathlib environment | Pass, 16/16 original closure modules and 3/3 final delta modules, exit 0 | Full repository-owned import closure; two revised owners and audit rechecked |
| Kernel axiom dependency output | Pass, 67/67 expected reports | All 49 new theorems, eight new constructions, ten reused declarations |
| Foundational axiom union | `propext`, `Classical.choice`, `Quot.sound` only | Actual `#print axioms` output |
| Independent placeholder/bypass text scan | Zero findings | Six new Lean files |
| Maintained `axiom_audit.py --fail-on-gaps` | Pass, exit 0, 6/6 read, zero gaps | Exact six new Lean files |
| Maintained staged proof gate | Pass, exit 0 | Exact six staged Lean files after proof refinements |
| Maintained semantic content gate | **Exit 2; not passed** | 6/6 selected files read, zero findings; global importer inventory has 1,114 unreadable paths |
| Actual root-package locked Lake build | **Exit 1; blocked** | Missing `external_refs/homotopy-hypothesis-lean4` prevents package loading |

The 1,114 failures are all in the semantic tool's global importer-reading
phase, even though the file-prefix selection contains only the six new
files. They do not become a passing gate merely because the selected files
have zero findings. Likewise, isolated pinned source compilation does not
certify the root Lake package.

Independent QA used the maintained file wrapper for each closure source:

```bash
python3 tools/infra/run_locked_lean.py \
  --lake /workspace/scratch/da3b6dcb8ab1/verification-runtime/lake-isolated \
  lean/InfoGeometry/OperatorAlgebra/StructuredOperatorAudit.lean \
  -o /workspace/scratch/da3b6dcb8ab1/info-geometry-lean/.lake/build/lib/lean/InfoGeometry/OperatorAlgebra/StructuredOperatorAudit.olean
```

The same form of command was run in dependency order for the other 15
repository modules. The adapter invokes the actual pinned Lake/Lean binaries
against an independent checkout of the unchanged pinned Mathlib revision;
it supplies no replacement axioms or source stubs. A managed-runtime loader
shim resolves the compiler executable path; it does not change Lean's kernel.

The separate root-package attempt used the real root Lake configuration:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Routing.InvolutiveDiagonalAlgebra \
  InfoGeometry.OperatorAlgebra.MonarchFactorization \
  InfoGeometry.Routing.SymmetricCausalBoundary \
  InfoGeometry.Krein.CayleyFormTransport \
  InfoGeometry.Krein.HyperbolicDepth \
  InfoGeometry.OperatorAlgebra.StructuredOperatorAudit
```

Both its maintained dependency-cache hydration attempt and its actual
`lake build` stop at the missing HomotopyHypothesis package. No dependency
pins, hooks, build gates, external-reference versions, or caches were changed
to conceal this failure. The branch is suitable for a **draft review** of
the checked theorem scope; whole-package integration is unresolved.

For the lexical audits, the exact six source paths above were passed to
`python3 tools/infra/axiom_audit.py --fail-on-gaps`. One invocation of
`python3 tools/quality/semantic_content_audit.py --gate` received six repeated
`--file-prefix` arguments, one for each complete source path. The independent
command ledger, timestamps, log hashes, reports, and compiler output are
preserved at
`/workspace/scratch/da3b6dcb8ab1/verification-runtime/structured-qa/` and
`/workspace/scratch/da3b6dcb8ab1/verification-runtime/structured-qa-delta/`.
The delta used the same locked file commands for `MonarchFactorization`,
`HyperbolicDepth`, and `StructuredOperatorAudit`, followed by the exact-six
debt audit and `python3 tools/quality/proof_proxy_staged_gate.py` with the
same six explicit paths. It did not repeat the already observed global
semantic-inventory or root-package failures.

### Checked source hashes

| Source | SHA-256 |
|---|---|
| `Routing/InvolutiveDiagonalAlgebra.lean` | `d1ab31688e07741de9332aad6743e9c08c554f3b69783dbe4bea4ae9908982ee` |
| `OperatorAlgebra/MonarchFactorization.lean` | `3103abc3e9af72f4dde2029a118bad2a30d3bcf7549661e2308f6b363a6c30ce` |
| `Routing/SymmetricCausalBoundary.lean` | `e39dbe69103b6417280d62d0f1ff12cac6e1af14c71b7fada61ce1327f7cc11a` |
| `Krein/CayleyFormTransport.lean` | `f037374d3b825e699e2cfef4a4b66015296989d4757a797367ef198e273f219b` |
| `Krein/HyperbolicDepth.lean` | `b7a75abf454fbc3d8bc2fb718d2b0783ab6c12a6f963b05105c9c65d37d5c32c` |
| `OperatorAlgebra/StructuredOperatorAudit.lean` | `477b25c481d35d521d7c89f996adcf1833989e0d8d4f6c27f83080231b710fd3` |

**Disposition:** `[kernel_verified]` for the listed declarations at their
stated types; `[accepted_limited_scope]` for this operator formalization;
`[countermodel_found]` for the encoded Monarch closure and depth-bound
overclaims. Remaining algorithms, hardware assertions, broader physical
interpretations, and root-package integration are not promoted.
