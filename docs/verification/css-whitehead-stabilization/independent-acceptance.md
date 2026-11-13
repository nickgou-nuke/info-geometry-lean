# Independent acceptance: constructive Whitehead stabilization

**Disposition: accepted with the stated finite algebraic scope.**

The fresh native source-closure check passed. All six selected modules rebuilt
with zero compiler warnings and no incremental reuse. The native axiom audit
checked **171 declarations** and found only `propext`, `Classical.choice`, and
`Quot.sound`. The five new owners contain **81 named theorems** and **146 native
declarations**; the unchanged Krein owner adds 16 named theorems and 25 native
declarations. Native counts include definitions and generated support declarations.

The strict semantic scan at warning threshold **exited 1**, with 18 reviewed
warnings and zero errors. Its exit status is preserved. All six strict
placeholder commands exited 0, with zero hard findings and 11 reviewed soft
findings. No banned proof token was found in the six selected owner sources.
The mathematical review found no unresolved blocker in this scope.

## Independence and frozen source

The reviewer did not author or modify any promoted source file. Source review
preceded a fresh build and audit; no development result was substituted for
acceptance. Validation ran under the repository's shared build lock, with no
concurrent build/test activity. The parent separately owns the actual root
build and publication hook; neither is certified by this report.

- Checkout: `/workspace/scratch/d18a558d1d7d/css-rigidity-lean`
- Base: `a392af178af1fe2bcba2ba39eb405700c6ee103c`
- Source checkpoint: `abd22cd4badf6df017cc85fa137cb2160f48eca9`
- Source checkpoint tree: `c3be031ec27e795572eb35eb0b25f46dff13f968`
- Toolchain: `leanprover/lean4:v4.34.1`
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`

The checkout was clean before and after independent verification. The source
hashes in the native report match the reviewed checkpoint. The existing
`KreinAdjoint.lean`, `lean-toolchain`, and `lake-manifest.json` are byte-identical
to the base. All nine inspected native package Git revisions match their
manifests. The sole dirty dependency path is the previously documented
Batteries `docs/README.md` type change; no dependency Lean-source change was
observed or made. Native dependency caches were used; this was not a source
rebuild of every dependency package.

## Coverage

| Selected owner | Named theorems | Audited native declarations | Fresh compile | Warnings |
|---|---:|---:|---|---:|
| `Algebra.ElementaryMatrixOperators` | 25 | 42 | passed | 0 |
| `Algebra.WhiteheadStabilization` | 10 | 14 | passed | 0 |
| `Algebra.StablePresentationEquivalence` | 17 | 43 | passed | 0 |
| `Algebra.StablePaddingEquivalence` | 13 | 21 | passed | 0 |
| `Algebra.HyperbolicPresentationTransport` | 16 | 26 | passed | 0 |
| `Canonical.SpinorialCore.KreinAdjoint` (unchanged) | 16 | 25 | passed | 0 |
| **Total** | **97** | **171** | **passed** | **0** |

These six modules are also the entire selected repository import closure.
The native audit enumerates every declaration by its owning module, including
private/generated support, rejects unsafe/partial declarations, and calls
`Lean.collectAxioms`. A separate assertion checked zero warnings for all six
modules because the maintained checker's automatic warning threshold is
specific to its original Clifford–Dirac prefix.

## Mathematical review

### Actual elementary operations

`ElementaryMatrixOperators` constructs native matrix units with explicit
inverses. Its elementary subgroup is the native subgroup closure of scalar-entry
off-diagonal transvections. The critical block-shear membership theorem is
proved using native `Matrix.induction_on'`: single entries give actual scalar
transvections, and addition of blocks gives multiplication of shears. No
structure field assumes the factorization being claimed.

### Ordered Whitehead stabilization

The balanced unit `diag(U,U⁻¹)` has an explicit ordered four-shear factorization.
Its scalar elementary subgroup membership is then derived from the preceding
owner. The rectangular identity uses `diag(V,U)` on the right; that factor
remains an arbitrary unit. Both identity-block and zero-row stabilization
retain multiplication order over an arbitrary `Ring`.

### Two distinct stable formulations

The move-generated formulation uses the native Sigma carrier and `EqvGen`.
An unrestricted basis move is realized by identity padding, an actual
left-elementary basis change, and reverse padding. Native closure induction
then proves equality of the ordinary and elementary generated relations.

The one-shot formulation directly matches the common-padding shape in the
paper's Definitions 13–14. `padding_eq_fromBlocks` certifies
`M ⊕ I_α ⊕ 0_{β,η}`. `BasisEquivalent` quantifies actual left and right units;
its equality is native Sigma equality. It does not permit arbitrary
existential row reindexings. Zero-row padding associativity is proved with
`Fin.cast (Nat.add_assoc ...)`, retaining the canonical order. Adding common
zero rows converts an ordinary one-shot witness into an elementary one.
This proves the algebraic statement of Proposition 1 directly.

No general theorem identifying the one-shot relation with the separate
`EqvGen` relation is claimed. That normalization is unnecessary for the two
independently proved ordinary/elementary coincidence theorems.

### Inverse-adjoint transport

Inverse and star each reverse products, so their composite constructs the
native unit-group homomorphism. The resulting injective hyperbolic block lift
preserves both symmetric and skew off-diagonal forms using the existing
`Krein.IsIsometry` predicate. Rectangular pairing transport retains the full
ordered expression. Arbitrary right generator maps preserve a zero pairing;
reflection of vanishing correctly requires invertible generator changes.

### Hypotheses and limits

The algebraic results retain arbitrary unital noncommutative coefficient
rings. Adjoint results add `StarRing`; only the explicit noncommutativity
witness requires `Nontrivial`. Finite matrix indices do not assume that the
coefficient ring is finite dimensional. Empty dimensions and the trivial ring
are allowed in the principal theorems. No determinant, division-by-two,
characteristic-zero, or inverse-of-a-nonunit convention is used.

This scope does not construct a physical Clifford circuit, lattice locality,
a CSS phase classification, Schanuel/Ext comparison, a Frobenius/coextension
equivalence, Koszul nonsplitting, or an analytic limit. It also does not claim
noncommutative left-module dual semantics from the matrix dagger identities.
The paper's commutative Laurent-ring and physical hypotheses remain separate.

## Individual heuristic finding dispositions

All 18 semantic warnings are `trivial_surface`; all 11 placeholder soft
findings are `skeletal-proof`. They cover 19 distinct declarations. Every
finding is retained in the machine record with its check, location, and
individual disposition. The following table gives the complete review:

| Declaration | Review |
|---|---|
| `coe_elementaryUnit` | Definitional coercion to the explicitly constructed value 1 + single(i,j,a); both inverse equations are proved in elementaryUnit. |
| `coe_elementaryUnit_inv` | Definitional coercion to the explicitly constructed inverse 1 - single(i,j,a), with both inverse equations already proved. |
| `coe_upperUnit` | Definitional value formula for an actual native unit; its inverse and elementary scalar-generator membership are separately constructed. |
| `coe_lowerUnit` | Definitional value formula for an actual native unit; its inverse and elementary scalar-generator membership are separately constructed. |
| `coe_reindexUnit` | Native Units.mapEquiv value formula induced by Matrix.reindexRingEquiv; membership transport is proved separately by subgroup closure induction. |
| `inverseAdjoint_apply` | Definitional evaluation of the constructed native monoid homomorphism. Its multiplication law uses both order reversals. |
| `coe_inverseAdjoint` | Native coercion compatibility between unit star/inverse and the underlying monoid operations. |
| `inverseAdjoint_involutive` | Uses native star_inv, inv_inv, and star_star to derive involutivity; no hypothesis supplies the desired equation. |
| `coe_hyperbolicLift` | Definitional value formula of the constructed block unit. Injectivity and both form-preservation results are separate substantive theorems. |
| `skewForm_conjTranspose` | Direct block-adjoint calculation of the concrete off-diagonal skew form; simplification proves the claimed sign change without assuming it. |
| `appendZeroRows_natAdd` | Evaluation in a newly appended zero row. It supplies the canonical-index calculation used in the proved padding associativity theorem. |
| `coe_blockDiagonalUnit` | Definitional value of a native unit whose two-sided inverse was explicitly constructed from the component units. |
| `coe_balancedUnit` | Definitional value diag(U,U^-1); the four-shear factorization and scalar elementary subgroup membership are proved separately. |
| `stabilization_identity` | Substantive rectangular block multiplication. Native block multiplication and the unit inverse equations simplify the lower block to identity; multiplication order is retained. |
| `zeroRow_stabilization_identity` | Substantive rectangular zero-row transport. Native block-row multiplication and multiplication by zero prove the result; this is used to convert an ordinary padding witness to an elementary one. |
| `sharp_add` | Unchanged base owner. Expands sharp and proves additivity using star_add and distributivity in an arbitrary star ring. |
| `sharp_neg` | Unchanged base owner. Expands sharp and proves compatibility with negation using native star-ring identities. |
| `sharp_sub` | Unchanged base owner. Expands sharp and proves compatibility with subtraction using native star-ring identities. |
| `sharp_one` | Unchanged base owner. Explicitly conditional on J*J=1; star_one reduces sharp J 1 to J*J. It does not assert an unproved involutivity condition. |

Short proofs here either expose the value of an explicitly constructed native
object or derive a genuine identity through native simplification lemmas.
They do not hide assumptions in a witness packet. The main elementary-membership,
factorization, stable-conversion, and pairing-preservation proofs were also
read in full. Reviewing these warnings does not convert the strict semantic
command's exit code into a passing result.

## Exact commands

The fresh native command was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/66380c6bf432/info-geometry-lean/.lake/packages/mathlib \
  --lean /workspace/scratch/4796737fb777/lean-environment/lean-4.34.1-linux/bin/lean \
  --target InfoGeometry.Algebra.ElementaryMatrixOperators \
  --target InfoGeometry.Algebra.WhiteheadStabilization \
  --target InfoGeometry.Algebra.StablePresentationEquivalence \
  --target InfoGeometry.Algebra.StablePaddingEquivalence \
  --target InfoGeometry.Algebra.HyperbolicPresentationTransport \
  --target InfoGeometry.Canonical.SpinorialCore.KreinAdjoint \
  --output /workspace/scratch/d18a558d1d7d/css-rigidity-qa
```

It exited 0. Neither `--incremental` nor `--skip-audit` was supplied.
Afterward, the serialized static review script ran all six commands of the form
`python3 tools/quality/placeholder_audit.py --root <owner> --strict --json-out <report>`;
each exited 0. It then ran the semantic scanner on those same six owners with
`--fail-on warning`, which exited 1. All exact argument arrays, working
directories, outputs, statuses, source comparisons, and dependency states are
in `static-gates.json`. The actual script is retained as `run-static-review.py`.

## Evidence files and boundary

- `source-closure.json`: exact module graph, source/verifier hashes, compiler results,
  toolchain, native declaration counts, and allowed axiom union.
- `axiom-audit.txt`: complete native declaration audit output.
- `native-logs.json`: all six compiler logs, generated audit source, native environment,
  original evidence manifest, and full audit log.
- `static-gates.json`: exact strict commands, outputs, exit statuses, source counts,
  banned-token result, base comparisons, and native package revisions/status.
- `placeholder-findings.json`: all six complete placeholder reports.
- `semantic-findings.json`: the complete strict semantic report at warning threshold.
- `findings-dispositions.json`: all 29 heuristic findings with individual review.
- `evidence-sha256.json`: hashes of the preserved reviewer evidence.

The dedicated CI workflow was reviewed for the same target list, pinned native
cache, exact-source checker, all-target zero-warning assertion, and retained
semantic output. Its semantic command fails on errors; the independent local
check intentionally used the stricter warning threshold and preserved its
nonzero result. No remote CI outcome is claimed here.

Registering final owners in `Canonical.All` does not certify that aggregate or
other downstream consumers. Full root-workspace build, actual pre-push,
publication status, and remote CI results must be reported from their own
observed runs after this review. The build/test lane was returned to the
parent after the independent native and static commands completed.
