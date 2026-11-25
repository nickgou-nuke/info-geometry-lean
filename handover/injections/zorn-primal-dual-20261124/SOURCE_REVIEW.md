# Independent mathematical and source review

Date: 2026-11-24. Reviewer role: independent read-only mathematical/source audit
(A-A), separate from implementation and final QA acceptance.

Base commit: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.

## Verdict and evidence status

**PASS for mathematical correctness and theorem-boundary honesty of the six
new owners at the source identities below.** No mathematical falsehood,
replacement by a commuting surrogate, vacuous determinant statement, or
unsafe proof shortcut was found. No mathematical source repair is required
by this review.

**Native compilation and execution of the axiom audit are pending.** This
report is not a kernel-verification receipt, a whole-repository build
certificate, or final QA acceptance. The reviewer did not compile Lean, run
tests, acquire the build lock, edit Lean sources, or alter compiler processes.
Source reading, import inventory, file hashing, and read-only Git metadata
inspection support the findings recorded here. This report is the reviewer's
only authored artifact.

The checkout was relocated intact to
`/tmp/info-geometry-zorn-primal-dual-20261124`. All six Lean owners were
byte-identical at relocation. A subsequent bounded review accepted the
proof-body-only revisions in `ZornLeftInverse.lean` and `ZornPrimalDual.lean`
described below; the other four new owners remain unchanged. The earlier
public-import integration item is resolved: `lean/InfoGeometry/All.lean`
imports the four top-level new targets, covering all six owners transitively.
The hashes below identify this refreshed source checkpoint. Later Lean
changes require comparison and, where material, further bounded review.

## Reviewed files and source identities

Paths in this report are relative to the repository root. SHA-256 identifies
the inspected bytes, independently of later compiler or Git status.

| Reviewed owner | SHA-256 |
|---|---|
| `lean/InfoGeometry/Algebra/ZornLeftInverse.lean` | `46ad3b7f73e324ff2914ed19d5d1c6e244a610b45b49c4df4962ed7884c0d710` |
| `lean/InfoGeometry/Algebra/ZornLeftDeterminant.lean` | `a45e8ccd3fc82182c68a01614669543f995a1ce7c8435d95535d32035be9f155` |
| `lean/InfoGeometry/Algebra/ZornPrimalDual.lean` | `9ef2e4467d67cc3ced74b3c641d7f3fbb6fb53586a7266829594fadebf3ab3b9` |
| `lean/InfoGeometry/Algebra/ZornChiralOperatorReconstruction.lean` | `94806af215c43ece8f5f79e6c99af71cefb993462ab850844b6363271a02399a` |
| `lean/InfoGeometry/Canonical/SouriauAffineActionGroupoid.lean` | `a6fcb4b8509f357247876b810199975fb7dc1c22881f5835baac2e7473ee82e6` |
| `lean/InfoGeometry/Geometry/SouriauCotangentGraphSigns.lean` | `7bcc993fed599eb1678656da73b963cda1effdb79dbc6aa64c622d45d86c778f` |

Additional inspected source surfaces:

| Surface | SHA-256 |
|---|---|
| `lean/InfoGeometry/Lie/SplitOctonionCliffordAction.lean` | `09b1da1216cd3cf95288b62c016cfce46eb85eefeac0ee72bcef89ce5f0ea382` |
| `lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean` | `dc8570a47bced3215ed0415998d5d7fe9390b79611d45f34b9e2c5e6c558f1f6` |
| `lean/InfoGeometry/All.lean` | `03ea0afb973145301ac222633397c22d373e0865be507040586c97e55af039fe` |
| `verification/zorn-primal-dual/check.py` | `058387aaf1bfc61a25de3066953f8a9224c398846ade4400b68aa5b401127912` |
| `verification/zorn-primal-dual/Audit.lean` | `99478268caca662b8b55e5c81b4ab3b233f77abd4a2b141ff863ecc664f60a7d` |
| `handover/injections/zorn-primal-dual-20261124/README.md` | `6f5e5a84cd9efe6498687f9afedbeace1f29af6aa210d36f3ee4c098768e6aec` |

## Bounded proof-repair review

The following original identities remain recorded as review history; the
tables above give the current identities.

| Changed surface | Earlier reviewed SHA-256 |
|---|---|
| `lean/InfoGeometry/Algebra/ZornLeftInverse.lean` | `4879ec6b52437c38c9d09310d7875321bda35474256efee3b4cbe4f558a0d22c` |
| `lean/InfoGeometry/Algebra/ZornPrimalDual.lean` | `2f997ed5118046fa939f86bdcdb52074ec7393613f4b52ce714b4ee515a78017` |
| `verification/zorn-primal-dual/check.py` | `9af5dd3aa914ba5bddb99a526e119998eafa92b15405a0ee773768bfcec9db1e` |

**PASS for the bounded semantic re-review.** The current proof changes leave
all theorem statements, hypotheses, definitions of mathematical objects,
carriers, and operations unchanged. Reversing just the listed replacements
in memory exactly reproduced both earlier Lean file hashes, confirming that
there were no other byte changes in those two owners.

- `InfoGeometry.Algebra.ZornLeftCAR.conjugate_leftMultiplication_mul` now
  applies `LinearMap.ext`, introduces the whole Zorn argument, and explicitly
  changes the pointwise goal to the existing `kirmse_left` identity. This
  avoids the earlier recursive `ext` invocation descending into the Zorn
  coordinates before applying a lemma whose conclusion is equality of whole
  Zorn values. The contraction and its hypotheses are unchanged.
- The additive and scalar map-law proofs for `ZornPrimalDual.primal` and
  `ZornPrimalDual.dual` now use the existing coordinate simplification API
  directly. The four-vector-to-Zorn functions themselves are unchanged.
- `ZornPrimalDual.norm_encode` uses `simp ... <;> ring`, removing an explicit
  redundant addition unfolding and applying normalization only to remaining
  goals. The evaluated norm and Lorentz pairing are unchanged.
- The diagonal and parity section proofs explicitly change the evaluation of
  `hyperplane` to its scalar polynomial before `ring`. The diagonal
  polynomial is the difference of four coordinate products; the parity
  polynomial negates each spatial factor, giving the sum of four squares.
  These are definitionally the same goals as the previous simplification
  proofs, without any new assumption.

These are source-level proof repairs. Their acceptance here does not assert
that the compiler has accepted the revised terms; the native execution
status below remains pending.

## Preserved source mapping

The supplied prose and proposed code are inputs, not evidence that their
assertions were previously verified. They remain separately preserved in this
handover directory.

| Input | SHA-256 | Formalization disposition |
|---|---|---|
| `souriau-source.txt` | `849a749a4b8c387fc806d45c6e5a09ff69b928bd5618ff1aa353bd2b39b98799` | Algebraic action groupoid, inverse cocycle evaluation, finite Massieu transformation/midpoint result, and exact graph-sign correction; analytic and smooth geometric extensions remain outside the proved statements. |
| `zorn-source.txt` | `cf125e1522387dee1f391edeb82e4fd06e197465858685761b385c133d7383c6` | Primal/dual encoding, norm pairing, incidence, operator recovery, associator sign, inverse, and actual determinant, with full-Clifford faithfulness corrected. |
| `zorn-code-source.txt` | `3f12310b389e0bb09a0134782fbc7040fec68f204f1750e44bd6f39c1254b10a` | Proposed duplicate carrier/module construction is replaced by reuse of existing repository owners; accepted claims become the six focused owners. |

The following table maps mathematical phrases to the reviewed declarations
and the precise boundaries that must be preserved in reporting. Each
namespace is written explicitly; a source filename is not being used as a
declaration namespace. In particular, `ZornLeftInverse.lean` adds declarations
to `InfoGeometry.Algebra.ZornLeftCAR`, chiral recovery lives in
`InfoGeometry.Algebra.ZornVectorMatrix`, and both existing Clifford files add
declarations to `InfoGeometry.Lie.SplitOctonionImaginaryAction`.

| Mathematical content | Lean namespace and declarations | Boundary |
|---|---|---|
| Two independent four-vectors encode one Zorn element | `InfoGeometry.Algebra.ZornPrimalDual`: `encode` | A real linear equivalence from a product of two four-dimensional spaces; no identification of the whole eight-dimensional norm with a four-dimensional form. |
| Zorn norm equals primal/dual Minkowski evaluation | `InfoGeometry.Algebra.ZornPrimalDual`: `norm_encode` | The pairing is `(+---)` and the vectors are independent. |
| Genuine hyperplane incidence | `InfoGeometry.Algebra.ZornPrimalDual`: `hyperplane_eq_zero_iff`, `hyperplane_ker_finrank`, `incident_iff_not_isUnit`, `incident_iff_det_eq_zero` | A dimension-three hyperplane requires `p != 0`; projective quotienting is not constructed. |
| Chiral squares and contraction | `InfoGeometry.Algebra.ZornPrimalDual`: `primal_square`, `dual_square`, `primal_operator_square`, `dual_operator_square`, `mixed_operator_anticommutator` | The generic mixed anticommutator retains both time-coordinate operator terms. |
| Conjugate inverse | `InfoGeometry.Algebra.ZornLeftCAR`: `leftMultiplicationUnit`, `leftMultiplication_isUnit_iff` | Real endomorphism invertibility is equivalent to nonzero split norm. |
| Determinant | `InfoGeometry.Algebra.ZornLeftDeterminant`: `leftMatrix_det`, `leftMultiplication_det` | Actual eight-dimensional left-action matrix and endomorphism, with an explicit coordinate bridge. |
| Peirce and Majorana recovery | `InfoGeometry.Algebra.ZornVectorMatrix`: `left_E11_reconstruction`, `left_E22_reconstruction`, `left_U_reconstruction`, `left_V_reconstruction` | Uses the existing left action and existing signs. |
| Source-ordered volume and nonassociativity | `InfoGeometry.Algebra.ZornVectorMatrix`: `leftMajorana_source_ordered_volume`, `leftMajoranaPlus_associator_witness`, `leftMajoranaPlus_not_multiplicative` | Volume is `-I`; source convention gives associator witness `-2 q7`. |
| Native seven-generator Clifford representation | `InfoGeometry.Lie.SplitOctonionImaginaryAction`: existing `splitOctonionLeftCliffordRepresentation` | A Mathlib Clifford algebra homomorphism into endomorphisms; octonions remain the representation module. |
| Failure of full-Clifford faithfulness | `InfoGeometry.Lie.SplitOctonionImaginaryAction`: existing `leftClifford_finrank`, `canonicalZornEnd_finrank`, `splitOctonionLeftCliffordRepresentation_not_injective`, `splitOctonionLeftCliffordRepresentation_kernel_finrank_ge` | Domain dimension 128, target dimension 64, kernel dimension at least 64; vector-map injectivity remains compatible with this. |
| Affine action groupoid | `InfoGeometry.Canonical.SouriauAffineActionGroupoid`: `AffineActionGroupoid`, `nonempty_hom_iff` | An algebraic groupoid of elements of the actual affine action. |
| Massieu signs and curvature direction | `InfoGeometry.Canonical.SouriauAffineActionGroupoid`: `inverse_cocycle_eval`, `neg_twistedMassieu_ad`, `neg_twistedMassieu_midpoint` | Finite nonempty ensemble; the new inequality is midpoint concavity. |
| Invariant affine/Massieu expression | `InfoGeometry.Canonical.SouriauAffineActionGroupoid`: `affine_pairing_add_massieu` | Identifying this expression with entropy requires additional mean/gradient relations. |
| Cotangent graph sign | `InfoGeometry.Geometry.SouriauCotangentGraphSigns`: `twistedPairing_graph_scaled`, `twistedPairing_positive_graph`, `twistedPairing_negative_graph` | Algebraic graph restriction, not a smooth symplectic-reduction theorem. |

## Carrier reuse and mathematical checks

### Zorn left inverse

The new owners use the existing `InfoGeometry.Algebra.ZornVectorMatrix ℝ`
with fields `a,v,w,b`, its actual cross-product multiplication, its existing
real module, and `ZornLeftCAR.leftMultiplication`. No second octonion carrier
or associative octonion instance is introduced.

The inverse owner reuses
`InfoGeometry.Algebra.ZornVectorMatrix.kirmse_left`, supplied by
`Algebra/ZornDerivationBridge.lean`, to establish both orders of conjugate
contraction:

\[
L_{\bar z}L_z=N(z)I,\qquad L_zL_{\bar z}=N(z)I.
\]

For nonzero norm, the proposed inverse is exactly
\(N(z)^{-1}L_{\bar z}\). Necessity of nonzero norm follows from the action of
an inverse on octonion one and multiplicativity of the norm. This reasoning
does not import octonion associativity or positivity of the split norm.

### Primal/dual geometry

The explicit linear equivalence `encode` exhausts the carrier rather than
merely selecting a diagonal subset. The incidence functional is

\[
\eta(x,p)=x_0p_0-x_1p_1-x_2p_2-x_3p_3.
\]

Evaluation on the four coordinate basis vectors proves that the functional
is zero exactly for `p = 0`. Rank-nullity for a nonzero functional then yields
the dimension-three kernel. This prevents treating the entire space obtained
when `p = 0` as a genuine hyperplane.

The full mixed relation is correctly stated as

\[
L_XL_P+L_PL_X=p_0L_X+x_0L_P-\eta(x,p)I.
\]

The diagonal and parity sections give the Minkowski and Euclidean squares.
These are restrictions of the full split norm. The source corrections are
consistent: the full norm has signature `(4,4)`, its imaginary restriction has
signature `(3,4)`, and the negative imaginary norm is the Clifford form of
signature `(4,3)`. No separate signature-classification theorem is claimed
to have been newly introduced by these six owners.

### Matrix determinant

The coordinate equivalence identifies the Zorn carrier with functions on
`Fin 4 ⊕ Fin 4`. The concrete block matrix is intertwined with genuine left
multiplication. The cross-product signs in its two off-diagonal blocks agree
with the owned multiplication.

Writing `s = v dot w`, the matrix has form

\[
\begin{pmatrix}aI_4&B\\C&bI_4\end{pmatrix},\qquad BC=CB=sI_4.
\]

For `a != 0`, an explicit block factorization yields
\(a^4(b-a^{-1}s)^4=(ab-s)^4\). For `a = 0`, exchanging the two four-row blocks
has sign `+1`, because it exchanges four row pairs; the determinant reduces
to \(\det(CB)=s^4\). The final theorem is unconditional in `z`.

The coordinate bridge makes the carrier's finite dimension concrete. The
endomorphism determinant theorem is therefore not exploiting a fallback
value of determinant on an unestablished infinite-dimensional carrier.

### Chiral operators and Clifford boundary

The existing conventions are

\[
M_i^- = L_{U_i-V_i},\quad M_i^+ = L_{U_i+V_i},\quad
\Gamma=L_{E_{11}-E_{22}}.
\]

For the source's conventions,
\(q_i=V_i-U_i\), \(q_{i+3}=U_i+V_i\), and
\(q_7=E_{22}-E_{11}\), this gives the claimed source-ordered operator volume
`-I`. The associator witness, after evaluating the operator defect on `q6`,
is the octonion identity

\[
(L_{q_4}L_{q_5}-L_{q_4q_5})(q_6)
 =2(E_{11}-E_{22})=-2q_7.
\]

The pre-existing seven-generator lift uses the repository's `CanonicalZorn`
carrier. Its compatibility with the vector-matrix presentation is supported
by the existing `Algebra/Zorn/CanonicalVectorMatrixBridge` coordinate
equivalence and its addition, scalar, unit, and multiplication preservation
lemmas. The six new owners do not redefine that older carrier or lift.

The inspected existing noninjectivity source uses the exterior-algebra
dimension formula and actual eight-dimensional module dimension to obtain
`128 > 64`, and rank-nullity for the kernel lower bound. The dimension
obstruction is valid. Neither the new owners nor these inspected two existing
Clifford owners establish irreducibility, image equal to all of `M8(ℝ)`, or
identification of a selected simple component. Those stronger statements
must remain outside the claimed result.

### Souriau action and thermodynamic expressions

The action construction uses the actual existing affine coadjoint cocycle,
not a structure field assuming the desired groupoid theorem. Mathlib's
`Functor.Elements` construction has the applicable `Groupoid` instance; the
audit includes a concrete instance-synthesis example.

The inverse cocycle and finite Massieu transformation signs are correct.
The midpoint inequality follows from the finite exponential partition
function, finite Cauchy-Schwarz, positivity, and logarithm monotonicity.
The hypotheses include a finite nonempty state space.

`invariant_on_arrow` is explicitly conditional on invariance of the input
function. `affine_pairing_add_massieu` supplies the concrete cancellation
identity, but no mean/gradient identification is added here. This supports
invariance of the stated expression, without by itself constructing a
Legendre entropy.

No smooth symplectic groupoid, infinite ensemble/integration theorem,
covariance Hessian identity, full concavity theorem, or general Legendre
duality theorem is established by these new files.

### Skew graph signs

For the owned convention

\[
\Omega((u,\mu),(v,\nu))=\nu(u)-\mu(v)+B(u,v),
\]

the graph \(\mu=cB(u,\cdot)\) pulls back to \((1-2c)B\). Therefore the
positive graph gives `-B`, while the negative graph gives `3B`. The
non-equality statement assumes an actually nonzero value of `B`; it is not
vacuous. Closedness, nondegeneracy, and smooth reduction are not asserted.

## Validation-source review and pending checks

The driver at the recorded identity checks Lean `v4.34.1`, the pinned Mathlib
revision `d13f23b723b8a846827a245b89c10fc7d3f11612`, all supplied cache package
revisions, and clean tracked dependency sources. It records a compiler binary
hash, manifest hash, checker hash, dependency paths/revisions, source hashes,
commands, outputs, and a uniquely identified receipt. Its compiled-source
cache is keyed by the recorded environment.

The source hashes are computed after acquiring the maintained build lock.
The launch-time checker hash is checked again after waiting, and source,
checker, audit, and manifest stability are checked before recording success.
The measured compiler/dependency environment is recomputed after waiting and
again before success. Caught exceptions and Python-handled interruption record
a non-success receipt; external termination can leave an incomplete receipt,
as documented in the final checkpoint below. Native invocations now use `-j1`, inherit the shared build-lock file
descriptor, write per-module logs, and periodically report sampled peak RSS
and elapsed time. These source changes address the earlier stale-checker,
pre-lock source-hash, and resource-observability concerns. Independent runner
trust/QA review remains a separate role.

The current default import closure contains **38 repository modules**,
including the two existing Clifford owners. A separate read-only import
inventory found only ordinary single-module import lines throughout that
closure, so the current parser covers this actual source set. This is not a
whole-repository closure or umbrella compilation.

At the earlier environment inspection, all eight supplied cache package
revisions matched the root manifest: Mathlib, batteries, Qq, aesop,
importGraph, LeanSearchClient, plausible, and proofwidgets. Their tracked
source status was clean, and their exposed namespaces showed no
`InfoGeometry` shadow or unexpected second `Mathlib` provider. These are
observations at that inspection, not a substitute for the final runtime
fingerprint.

`Audit.lean` inventories declarations by their actual owning module for the
six new owners and the two existing Clifford owners. It checks that each
selected owner was imported and contributes declarations, rejects unsafe or
partial declarations, and permits only `propext`, `Classical.choice`, and
`Quot.sound` among collected axioms. This describes the inspected audit
program; **its execution has not yet supplied a passing result**.

A refreshed source token scan of the six new owners found no `sorry`, `admit`, `axiom`,
`native_decide`, `unsafe`, or `partial` token. Token scanning, source review,
native compilation, and executed axiom audit are distinct forms of evidence.

### Observed native receipt checkpoint

The reviewer read the generated receipts without running or interrupting any
compiler. At this checkpoint they record:

| Run ID | Observed result |
|---|---|
| `2ca20f63ed3644ae965cb7a887dfdbd9` | Earlier preflight failure, `KeyError: 'rev'`; no module compiler command or axiom audit was recorded. |
| `18cedb46b7f6412eb62f5df0da4c9e37` | First native compilation attempt, started `2026-11-24T09:07:07.783879+00:00` and finished `2026-11-24T09:20:10.946457+00:00`; status `failed`. Its first existing owner, `InfoGeometry.Algebra.ZornVectorMatrix`, returned `-9` (SIGKILL), with empty compiler output. No successful module command or axiom-audit result was recorded. |
| `df833b8d4ffc4303b623ffc5c7c0bed4` | Retry started `2026-11-24T09:24:34.929801+00:00`; receipt status `running`, with no module command or axiom-audit result yet recorded. The implementation owner reports it waiting for the shared build lock. |

The implementation owner reports resource exhaustion for the SIGKILL. The
receipt itself establishes termination by that signal, not its external
cause, and contains no Lean proof diagnostic. None of these receipts supplies
a successful native verification result for this handover. A later successful
receipt must replace the pending execution status; it must not be inferred
from the semantic source-review verdict.

## Completion boundary

The mathematical source review has no outstanding repair request. Public
import wiring is now present. The remaining acceptance evidence is native
compilation, executed axiom audit, the independent QA decision, and comparison
of any repaired sources against this snapshot. Final reporting must cite the
actual successful receipt and its exact scope rather than treat this source
review as execution evidence.

## Handover README review

The handover `README.md` at the additional identity above was read against the
reviewed theorem statements. Its mathematical statement boundaries pass
source review, with no required wording repair identified. It distinguishes
the full split norm from the four-dimensional sections, element multiplication
from associative operator composition, vector injectivity from full-Clifford
noninjectivity, kernel incidence from projective quotienting, and the finite
Souriau and bilinear-form results from stronger analytic or symplectic claims.

The README also preserves the complete mixed anticommutator, both inverse
orders, the actual matrix/action determinant bridge, the `-2 q7` evaluated
defect sign, and the `(1-2c)B` graph coefficient. Its section on reproduction
describes the focused 38-module driver and eight-owner axiom audit without
claiming a whole-repository or pre-push certificate. The proof-body repairs
reviewed above do not change these statement boundaries, and this
documentation review does not change the pending native execution status.

## Final blocked checkpoint

This observation supersedes the earlier queued/running observation for retry
`df833b8d4ffc4303b623ffc5c7c0bed4`. The implementation owner reports that the
queued tool session was externally interrupted while still waiting for the
shared build lock, and the tool returned exit code `130`. No Lean compilation
command or axiom audit began in that retry. The runner's cleanup did not
execute, so its raw receipt still says `running`; that is an **incomplete
receipt**, not evidence of continuing work or successful validation.

The reviewed Lean source identities above remain unchanged. The mathematical
source-review verdict remains separate from **native acceptance, which is
still pending**. Neither the interrupted retry nor the earlier SIGKILL
supplies a passing kernel or axiom-audit result. The README hash above records
the earlier reviewed mathematical narrative; subsequent status-banner edits
do not change the theorem boundaries or create execution evidence.

See [VALIDATION.md](VALIDATION.md) for the packaged validation status and the
next reproduction step. This report does not certify a completed focused
build, whole-repository build, or pre-push gate.
