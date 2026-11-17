# Projected full Zorn Gram: source and verification review

Date: 2026-11-17. This is a draft extension of [PR #384](https://github.com/nickgou-nuke/info-geometry-lean/pull/384), pinned at `6a0971cfb93e614ecccd29a44274f9bbf98706ae`, whose parent is main `08c34e03f610b452e03422037949196dc7d92d6d`.

**Disposition:** independent mathematical/source review and all scoped source checks pass at the identities below. Fresh native elaboration, zero target warnings, compiled declaration-axiom acceptance, and broader integration remain outstanding. The parent PR's initial native run failed; its actual failures are repaired in this branch. No native pass is inferred from source review or publication.

## 1. Exact integrated scope

| File | SHA-256 | Scope |
|---|---|---|
| `lean/InfoGeometry/Algebra/ZornAssociatorGram.lean` | `6f96d600df68ad5fd05f5b9cbd9668d0c816448951ee0c454696e3c969e3abec` | Repair seven actual elaboration errors in the existing full-family Gram owner; preserve every declaration, statement, definition, carrier and import |
| `lean/InfoGeometry/Algebra/ZornProjectedAssociatorGram.lean` | `856a263b3968334a6bbe8321a94534ea6ca7a2649e03856f4caabd209c123746` | Construct the energy projection and compressed bilinear form; prove the exact quadratic zero set and left radical, including both trace cases and zero energy |
| `docs/sources/zorn_projected_gram_intake_20261117.txt` | `1fef0d88c605c9d59f6590503b776362454f6b30b5022bbdec25dc1b12960e48` | Preserve the complete 36,565-byte supplied input without normalization |
| `.github/workflows/zorn-projected-associator-gram.yml` | `0a377941312fb42c5359a0e47394fea861b24b9a93d64c3938022905fc5f4a6c` | Dedicated fresh native/source acceptance for both changed owners |

The two definitions and 19 theorem declarations counted in the new source are a textual inventory. Native owned-declaration counts must come from the compiled-environment audit; no textual count is substituted for that result.

The base owner formerly had SHA-256 `47af00b942f4b34e4aa36b63b6b4ebb43b0fdb22b6618e8fde97c575fae4ef8d`. No earlier result is transferred to different source bytes. The exact base commit and all three files introduced by PR #384 were reconstructed locally and verified against their remote Git blob and tree identities before this extension was applied.

## 2. Mathematical/source review

The new file reuses the actual real Zorn carrier, its nonassociative multiplication, the positive coefficient pairing, all 64 inherited ordered associator probes, and the existing main normalized-dyad construction. No scalar replacement, reduced family, assumed kernel packet, or external physical axiom is introduced.

For every energy vector `h`, the projection `P_h` annihilates `h` and has image perpendicular to it in the positive coefficient pairing. The normalized dyad uses Lean's total inverse, so `P_0` is the identity. This supplies a defined value at zero, not a smoothness or continuity theorem there.

The exact result is

```text
G_h(x,x) = 0
  iff exists a b : Real,
    x = a • h + b • one and b * (h.a + h.b) = 0.
```

The same condition describes the bilinear left radical. The scalar coefficient condition follows from pairing `P_h(x) = b • one` with `h`. The reverse implication uses projection annihilation and orthogonality. The radical proof uses the full Gram radical theorem; it does not assume that `P_h` is surjective.

Independent review checked the full source, zero-energy and trace cases, exact API statements, and the existing main pairing/dyad/no-go proof bodies. The trace-zero simplification retains both scalar and energy directions. The trace-nonzero simplification retains exactly the energy line. The theorem is pointwise finite bilinear algebra; it does not establish a Hilbert endomorphism identification, global dynamics, Gibbs convergence, heat exchange, or physical uniqueness.

The [contract and intake ledger](ZORN_PROJECTED_GRAM_CONTRACT.md) records the motif-to-mathematics map, causal proof order, existing-main reuse, exact overlapping PR revisions, and the invalid stronger claims in the input.

## 3. Actual parent failure and exact repairs

[Run 44058459909, job 133953777692](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44058459909/job/133953777692) checked merge revision `72e353bfb7276d25d0b7bd560aa3dbfd2b7ad82b` for head `6a0971cfb93e614ecccd29a44274f9bbf98706ae`. Checkout, unchanged pins, and cache acquisition succeeded. All 18 repository dependencies compiled. The target `ZornAssociatorGram` failed with seven errors and zero warnings; no subsequent axiom acceptance was obtained.

Artifact `14321217722` has ZIP SHA-256 `4e29881b02461e54935d0212c1c78ef847a690bfcd25a33ac71fc2d54289d27a`. All 19 archived source hashes were independently reconciled with the report, and the target source matches the inspected PR head exactly.

| Actual error | Included repair |
|---|---|
| Two alternative-law constants were named under the wrong namespace | Use the existing `InfoGeometry.Algebra.zorn_left_alternative` and `zorn_right_alternative` |
| Two zero-pairing goals expanded native zero into an explicit Zorn record prematurely | Use restricted native `map_zero` and `LinearMap.zero_apply` rules |
| The zero bilinear map was not evaluated after basis extensionality | Simplify its two applications with `LinearMap.zero_apply` |
| Canonical/vector associator transport retained incompatible bundled/explicit operation forms | First transport canonical operations, then normalize only the vector operations with their existing definitions |
| Scalar transport retained explicit Zorn scalar multiplication | Use the existing `zvm_smul_def` normalization |

The associator transport intentionally uses two phases so generic subtraction normalization cannot prevent the canonical subtraction transport. No global simp attribute or algebra instance is changed.

The compiled parent dependencies also reported 67 baseline warnings: 27 in `ZornPinorReconstruction`, four in `ZornCARAdjoint`, 18 in `SplitOctonionClassificationCore`, and 18 in `Zorn.CanonicalVectorMatrixBridge`. These are not represented as zero-warning target acceptance and are not repaired by changing unrelated owners.

## 4. Actual scoped source checks

Receipt: `/workspace/scratch/a6c715447467/verification/zorn-projected-source/receipt.json`. It binds both current Lean hashes to the following actual commands and exit statuses.

| Check | Observed result |
|---|---|
| Strict placeholder audit of `ZornAssociatorGram` | Exit 0, one file scanned, zero hard findings, one soft finding |
| Strict placeholder audit of `ZornProjectedAssociatorGram` | Exit 0, one file scanned, zero hard findings, one soft finding |
| Semantic-vacuity gate at `--fail-on error` | Exit 0, complete two-file selection/read coverage, zero errors, four warnings |
| Strict OpenGauss screener | Exit 0, no violations or quarantine packets |

The old Gram soft finding is the native eight-element basis cardinality proof using ordinary kernel `decide`. The new soft finding is the short trace-zero corollary, which simplifies the proved general kernel theorem under the stated trace hypothesis. The four semantic warnings identify the pairing-with-unit readout, the definitional compressed-form application rule, and the two derived energy-annihilation equations. Their exact mathematical roles were reviewed. They are not proof holes or unproved positivity/kernel assumptions. Findings and thresholds remain unchanged.

These source checks do not certify Lean elaboration or actual compiled axiom dependencies.

## 5. Dedicated workflow and remaining gates

The maintained source resolver gives **24 repository modules**: both audited targets and 22 dependencies. There are **33 direct native Mathlib import roots**. The reused `RegularDyadCompression` already imports the full `Mathlib` umbrella; this is disclosed rather than silently narrowing or replacing that owner. Four additional repository dependencies compared with the parent Gram closure are the existing dyad, Peirce-compression, Peirce-decomposition and idempotency-defect owners; the new bridge supplies the twenty-fourth module.

The unchanged pins are Lean `v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The new workflow uses the unchanged maintained native checker, shared build lock, closure resolver and compiled declaration auditor. It checks the exact public event SHA, freshly compiles every resolved repository owner, forbids reused project outputs, rejects warnings on both selected targets, and audits every declaration owned by both. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; unsafe and partial declarations are rejected.

The workflow repeats source guards with complete target coverage and reconciles live/copied sources, checker/report identities, 17 named helper/pin/workflow/document/raw-input files, and resulting evidence. It uploads actual evidence even on failure and has read-only repository permissions. Runtime scope and declaration counts are computed from the actual closure/audit.

Independent syntax/structure review passed YAML parsing, all seven Bash payloads, all five embedded Python payloads, exact two-target reconciliation, source-path coverage, and hash bindings. The parent also reviewed the complete diff against the prior reviewed workflow. These results are source/configuration checks, not execution QA.

The actual maintained nonblocking lock probe observed another native build holding `/tmp/info-geometry-build.lock`. The lock is not bypassed, replaced, or treated as stale from its PID text. No local compiler result for this integrated candidate is claimed. Tracked hooks are installed; the actual normal staged-hook result and publication identity will be recorded in the PR body. Broader root-package/pre-push and whole-repository acceptance remain separate outstanding gates.

No merge is requested by this draft, and the parent PR's unresolved native acceptance is not hidden by the new source review. Fresh hosted evidence must establish both exact repaired owners together.
