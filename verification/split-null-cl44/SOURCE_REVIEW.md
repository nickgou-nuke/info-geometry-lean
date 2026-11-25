# Source review: canonical null incidence and real Clifford transport

## Evidence status

This record concerns source review and scoped source gates. Native compilation,
fresh warnings-as-errors elaboration, and native transitive axiom acceptance
are required separately. No claim of the uploaded module's successful
compilation or execution speed is adopted.

## Independent roles

- The mathematical reviewer parsed the literal uploaded table and found exact
  counterexamples to alternativity, norm composition, the trace identity,
  null rank four, and the asserted integer volume certificate.
- The owner-search author generated the two canonical trace/null-incidence
  candidates. The native API reviewer independently checked their types,
  hypotheses, normalization, owner alignment, and native projection/trace APIs.
  The integrating author inspected both candidates before applying them.
- The mathematical reviewer generated the native Born and real Dirac-transport
  candidates. The owner-search reviewer independently checked their carrier,
  isometry, Clifford transport, CAR, product order, and explicit volume signs.
  The integrating author inspected their implementation and resolved the
  recursive-extensionality risk before integration.
- The wrapper and workflow receive a separate read-only tooling review.
  Candidate authors did not edit tracked owners or run Lean builds.

## Exact owner inventory

These are explicit public declaration counts from source, not native
environment counts. The verifier also inventories private and generated
module-owned declarations when it runs.

| Owner | Public source heads | SHA-256 |
|---|---:|---|
| `Lie/CanonicalZornRegularTrace.lean` | 5 | `e7cff430ee3fbe2c9cdac3c6f3edccceb8fecf70c759c5b0f05e959c986b938e` |
| `Lie/CanonicalZornNullIncidence.lean` | 6 | `93f21de5c0ff1c95780b3b5ef1da1293022a4f95036faed8e770696f73706d32` |
| `Clifford/Cl44BornReciprocity.lean` | 12 | `ed2fe8b44eba251220e10903e2c9a8920d93582d2d60a994574aebaa0f63d828` |
| `Canonical/ZornCl44DiracTransport.lean` | 36 | `22a9c08b0293aa012f99dc54f8685e4728474207441de90638f936b5b553dc47` |

## Mathematical review

The full-null statements use the actual canonical real Zorn left regular
representation and retain exactly nonzero-element and zero-norm hypotheses.
They generalize the existing imaginary-only right-action result. The polar
form is Mathlib's unhalved `QuadraticMap.polar`: the partner has value one and
operator trace is four times that polar value. The projection
`L_conj(X) * L_Y` has image in `ker L_X` and fixes that kernel. Native
`LinearMap.IsProj.trace` supplies its dimension. No second multiplication
formula, basis, carrier, or custom idempotent trace proof was added.

The Clifford coordinate map groups the eight real coordinates into the
existing two quaternion coordinate blocks, then reuses
`cartesianZornLinearEquiv`. Its native isometry gives an actual Clifford
algebra equivalence between the two quadratic forms. The representation into
endomorphisms is an algebra homomorphism on `ZornMatrix ℝ × ZornMatrix ℝ`,
whose dimension is sixteen. No equivalence to the full endomorphism algebra
is asserted. No multiplicativity theorem for an additional octonion table is
silently attached to the quadratic isometry.

Both half-normalized Witt families, their CAR, and nilpotency are transported
from their existing owner. The Born word is the ordered product of the four
negative Clifford generators. It fixes positive generators and reverses the
negative generators under conjugation, hence exchanges the Witt families.
Its represented action is the actual coordinate reflection
`(a,b,x,y) ↦ (b,a,-y,-x)` on each sheet. The ordered positive word has actions
`(R,-R)`, so the represented volume acts as `(S,C) ↦ (S,-C)`.
These orientation statements are about the declared coordinate order.

The results do not assert a projective incidence classification, a Clifford
algebra classification isomorphism with all matrices, or physical phase-space
dynamics. The complete intake and countermodels remain in the contract.

## Validation design

The four-owner wrapper selects fifteen explicit reused declarations and six
required extra source files. Its shared transaction preserves the original
Zorn/Souriau defaults, exact pins, maintained shared lock, fresh elaboration,
native module ownership and axiom checks, and before/after source fingerprints.
The generalized transaction is the already reviewed interface from PR #448.
The ordinary root workspace remains a separate acceptance surface.

At intake, the local maintained nonblocking shared-lock probe returned busy
with owner `klein-operator-hierarchy:2`; no running job or lock was modified.
A queued or blocked local attempt is not native acceptance. The hosted route
checks the exact public commit and preserves available evidence on failure.

## Executed checks

At the four-owner checkpoint, the following commands exited zero:

- `git diff --cached --check`.
- `python3 -B tools/quality/proof_proxy_staged_gate.py`.
- `python3 -B tools/quality/placeholder_audit.py --strict` with all four owner
  paths: zero hard findings, six reviewed soft flags.
- `python3 -B tools/infra/axiom_audit.py --fail-on-gaps` with those paths:
  zero source-level open gaps.
- `python3 -B tools/quality/repo_lean_scope_audit.py` with those paths:
  zero debt or scope findings.
- `python3 -B tools/quality/semantic_content_audit.py` with one `--file-prefix`
  per owner and `--gate`: four selected files, zero findings.

The six placeholder heuristics flag the half-sum/half-difference readbacks
and ordered Born-product readbacks in the two Clifford owners. Their actual
types express linearity and algebra-homomorphism transport on the native
noncommutative carriers. They were inspected as part of the independent source
review; they do not assume the downstream CAR, involution, or grading result.

Both Python drivers parsed. The workflow parsed as YAML; all five run-step
shell snippets passed `bash -n`, and its two embedded Python programs parsed.
The configuration has eight workflow steps. A direct invocation of the actual
`source_snapshot` confirmed all six required extra files are tracked and
included. The original six Zorn/Souriau targets and seventeen reused declarations
remain the shared driver's defaults. The new wrapper selects four targets and
fifteen reused declarations. The independent tooling reviewer checked all
fifteen names against source and requested evidence-path triggers; both the
contract and raw-intake directory are now included in the workflow paths.

The reviewed mathematical sources have 59 explicit public declaration heads.
This count is not a native environment inventory. Native acceptance remains
pending until an exact-revision receipt says otherwise.

## First native run and reviewed repairs

[Native run 45406866384](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45406866384)
checked published head `acbb4c0e8184478f502b400af94c19b23d08297c` and
failed during its target build. The complete artifact `14927122918` was
downloaded and its SHA-256 matched GitHub:
`58786bc465b2e5a70f028516b0c70b0cc1e516f2b493d88bd445513f343d92d3`.

The compiler exposed two residual transport goals: the quadratic isometry's
definitional coercion after generator transport, and commuted sums of negative
coordinates in `bornReflection.map_add'`. The corresponding repairs add `rfl`
and `add_comm` at those exact goals. The Born owner also replaces deprecated
`if_neg` with the compiler-requested `ite_eq_right`. The three downstream
uses-sorry warnings were consequences of the failed reflection definition;
there are no authored proof holes.

The existing determinant dependency reached resource limits in its basis-entry
calculation and recursive minor expansion. The inherited Zorn workflow also
exposed the nonzero incidence witness's coordinate-reduction failure. Those
base-owner repairs are published on #442 at
`f2235ba8948a74a8c952e9a59775abc9e1cd05b0` and integrated here. The matrix
readout now compares eight generic coordinates using the native matrix/linear
map equivalence, and Mathlib's certified `eval_det` computes the determinant.
The same theorem statements, hypotheses, signs, coordinate order, and bounded
determinant budget are retained. The native incidence witness first uses its
existing coordinate theorem. The base source review records both failed runs
and artifact digests.

Independent source/API review accepted all four repairs. Updated target hashes:

| Source | SHA-256 |
|---|---|
| `Cl44BornReciprocity.lean` | `a7c6ecf3d84b17de15ecc5dbda0a5ab267de71414978ab603d6779bd5b5ba552` |
| `ZornCl44DiracTransport.lean` | `467d802ecb1564ca66192e4c55ee5006465206afd3e46cf2b9968d669a133946` |

The trace and full-null owners are unchanged. Their elaboration was not reached
because the determinant dependency failed. No acceptance claim is inferred
from that absence of diagnostics. A new exact-revision native transaction is
required for these repairs.

The repaired target pair passed the staged proof gate, whitespace check,
source axiom/debt and scope audits, and semantic gate (two files, zero findings).
The placeholder audit has zero hard findings and the same six reviewed
normalization/ordered-product soft flags described above. The base-owner pair
passed its corresponding source gates separately with zero placeholder findings.

## Successful target build and warning-only follow-up

[Run 45410443191](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45410443191)
checked `860458be8e974cfce0574a8e163d30bb4a6074d7`. **All four target modules
and their imported dependencies built successfully** (9,034 jobs). The repaired
determinant owner also built successfully. The subsequent fresh-source stage
failed with warnings treated as errors. Artifact `14929780737` has verified
SHA-256 `59a75489963889deffcfe588779520d11f3b6a190b4e2050f33e626583018803`.

The complete log contains exactly five diagnostics in the four selected owners:
two unnecessary sequential-focus warnings in the trace owner, and one deprecated
negation tactic plus two local-instance style warnings in the null owner. The
Born and Dirac transport owners have no diagnostics. The minimal follow-up makes
exactly the compiler-directed replacements: two `<;> ring` to `; ring`,
`push_neg` to `push Not`, and two proposition-local `letI` declarations to `let`.
Pinned Lean/Mathlib implementations confirm the same tactic engine and local
instance availability. No statements, hypotheses, imports, or mathematical
proof steps change, and no linter is disabled.

An independent reviewer checked the complete log and exact candidate diffs.
The updated source hashes are:

| Source | SHA-256 |
|---|---|
| `CanonicalZornRegularTrace.lean` | `529c5c9e4bee8ec363132263e73a0f33cfcd0aab31486c2676c42edcc6696104` |
| `CanonicalZornNullIncidence.lean` | `2f0abeeb69cb9da8ce7d09e44eec4a3bb3df61ff2ef65d4fe2760a4c32bd07b5` |

The successful target build is recorded at its exact revision. Fresh
warnings-as-errors elaboration and the final native declaration/axiom
transaction still require a successful receipt for the warning-only revision.

The two warning-only sources passed the staged proof gate and whitespace,
placeholder, source axiom/debt, scope, and semantic checks. Both scoped
placeholder and semantic audits reported zero findings.
