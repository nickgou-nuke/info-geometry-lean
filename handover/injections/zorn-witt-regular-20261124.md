# Zorn primal–dual regular operators: source and theorem contract

## Intake and provenance

- Source: the user's 2026-11-24 mathematical narrative and attached
  `Pasted text(20261124-084336).txt`.
- Exact attachment: `zorn-witt-regular-20261124-intake.txt` beside this record.
- Attachment SHA-256:
  `cf125e1522387dee1f391edeb82e4fd06e197465858685761b385c133d7383c6`.
- Source baseline: `66b240304293c9a99ae996d7c6714b558cbacf75`, the published
  head of PR #437, `codex/neutral-legendre-pauli-20261124`.
- Proposed branch: `codex/zorn-witt-regular-20261124`.
- Classification: finite representation-level algebra, risk R4 because the
  source multiplication is nonassociative. Statements that the attachment
  was already checked are intake claims, not compiler evidence.
- Roles: root authors/integrates the regular-norm owner and verification
  entrypoint; `audit_math` generates the isolated Witt-coordinate and exact
  determinant candidates;
  `source_scout` independently reviews the mathematical source and scope;
  `final_qa` performs independent acceptance checks. No author accepts their
  own proof packet.

The preserved attachment is evidence, not an instruction file or a promoted
Lean source. Its duplicate carrier and proof script are not installed.

## Formal objects and conventions

The carrier is the existing `InfoGeometry.Canonical.ZornMatrix ℝ`. Its module
structure and product come from `Canonical/ZornSpinor.lean`. The operator is
the existing `Lie.SplitOctonionEllCircularPeirceBasis.leftRegularRepresentation`
from `Lie/CanonicalZornRegularOperators.lean`, a linear map into
`Module.End ℝ (ZornMatrix ℝ)`. Endomorphism multiplication is composition.
The source product is not assumed associative.

The existing `Canonical.ZornClifford.zornNormFun` is
`a * b - dot x y`; its `zornConj` swaps `a,b` and negates both spatial slots.
The real four-vector pairing is the existing
`Lie.SplitOctonionWittVectorCovectorBridge.wittPairing`:
`x₀p₀ - (x₁p₁ + x₂p₂ + x₃p₃)`.

The four-vector-to-Zorn map is to be composed from the existing
`SplitOctonionWittPairingTransportBridge.toCoord` and
`canonicalToCoord.symm`. This is an actual linear equivalence, not a new
carrier or a new multiplication. Primal and dual elements are its values on
`(x,0)` and `(0,p)`. Hyperplane incidence uses the existing native functional
`toDualPlus p` and `LinearMap.ker`. The kernel is a proper hyperplane only
when `p ≠ 0`; at `p = 0` it is the whole four-dimensional space.

This is the Cartesian/diagonal Zorn identification in the attachment. It is
distinct from the separate Ell-circular Peirce frame; no equality of those
two basis transports is assumed.

An 8-by-8 matrix is `LinearMap.toMatrix b b` of the existing operator for an
actual `Module.Basis (Fin 8) ℝ (ZornMatrix ℝ)`. A basis change preserves the
determinant. No coordinate matrix is substituted for a different operator.

## Claim ledger

| Intake atom | Current owner or exact correction | Packet treatment |
| --- | --- | --- |
| Additive and module structure on split octonions | `Canonical.ZornMatrix`, transported from product coordinates | Reuse; no new instances |
| Full-carrier linear lift is injective | `leftRegularRepresentation_apply_one`, `leftRegularRepresentation_injective` | Reuse; this is linear injectivity |
| Two dual four-vectors give eight Zorn coordinates | Existing `toCoord` and `canonicalToCoord` equivalences | Compose them and prove the norm/regular-action readouts |
| Norm equals the primal–dual Lorentz pairing | Existing `zornNormFun`, `wittPairing`, and native coordinate equivalences | Prove their compatibility |
| General polarized left alternativity | `ZornVectorMatrix.associator_left_alternative`, existing vector-carrier `ZornLeftCAR.leftMultiplication_anticommutator`, canonical `canonical_left_linearized` | Expose the needed canonical regular-operator laws without a new operator |
| Chiral squares give nilpotents/idempotents | Actual canonical source product on the two selected four-planes | Prove `L_X²=x₀ L_X` and `L_P²=p₀ L_P` |
| Cross anticommutator is a scalar for general four-vectors | False without removing time/idempotent terms | Prove `L_X L_P + L_P L_X = x₀ L_P + p₀ L_X - η(x,p) I` |
| Conjugate contractions | `ZornClifford.mul_zornConj_mul`, `zornConj_mul_mul` over a commutative ring | Package both as equalities in native `Module.End` |
| Operator is invertible iff pairing is nonzero | Field-specific consequence; not valid from nonzero alone over arbitrary rings | Prove over ℝ, with explicit inverse and an incidence-kernel consumer |
| Singular iff incidence | Native matrix unit/determinant equivalence plus the unit theorem | Prove the exact zero-set statement |
| `det(L_Z)=N(Z)^4` | No exact owner found in the bounded source search; imaginary owner proves only `det(L_X)^2=Q(X)^8` | Added source-reviewed candidate `CanonicalZornRegularExactDet`; kernel validation is pending, and singularity does not assume this formula |
| Seven imaginary left actions yield a Clifford representation | `SplitOctonionCliffordAction.splitOctonionLeftCliffordRepresentation` | Reuse the actual `CliffordAlgebra` algebra homomorphism |
| Full `Cl(4,3)` action in `M₈(ℝ)` is faithful | Countertheorem `splitOctonionLeftCliffordRepresentation_not_injective`: source dimension 128, target dimension 64; kernel dimension at least 64 | Reject full-algebra faithfulness; keep generator-map injectivity |
| Nonassociativity disappears in operators | False: composition is associative but `L_a L_b = L_(ab)` generally fails | Reuse the associator-defect owners |
| Displayed defect on `(q₄,q₅,q₆)` is `+2q₇` | With the attachment's cross product and `q₇=U₋−U₊`, it is `−2q₇` | Correct the sign; the attachment's weaker inequality remains mathematically valid |
| Three negative-square left operators form a quaternion triple on the full module | The quaternion composition law is stronger than pairwise anticommutation; `ZornLeftCAR.gamma_operator_product_ne` supplies a counterexample | Describe three anticommuting real complex structures; do not infer the full-module quaternion relation |
| Minkowski, Euclidean, and neutral signatures are interchangeable | Full norm has signature (4,4); diagonal restriction is (1,3); spatial parity matched restriction is positive definite | State the chosen subspace/map; do not identify these forms globally |
| Point/momentum interpretation is a physical law | No dynamics or physical model supplied | Interpretation only |

The noninjectivity correction is already carried by
`Lie/SplitOctonionCliffordNoninjective.lean`, including
`leftClifford_finrank`, `canonicalZornEnd_finrank`, and
`splitOctonionLeftCliffordRepresentation_kernel_finrank_ge`. It is not a new
classification theorem in this packet.

## Smallest missing implications and consumers

1. `CanonicalZornRegularNorm`: lift existing source-level identities through
   the existing regular representation; prove an explicit conjugate inverse
   when the real norm is nonzero, its converse, and the determinant zero set.
2. `CanonicalZornWittRegularBridge`: compose existing equivalences; specialize
   norm, chiral squares, the true mixed anticommutator, invertibility, and
   singularity to the primal–dual pairing and the kernel of `toDualPlus`.
   A closed chiral-sum defect computes the corrected coefficient `−2`
   on the actual eight-dimensional carrier, and a closed upper/lower pair
   witnesses noncommutative operator composition.
3. `CanonicalZornRegularExactDet`: derive the actual native left matrix in
   the existing Cartesian basis, expand its sparse determinant one size at
   a time, and use native basis independence to obtain `N(Z)^4` in any
   genuine eight-element basis. This candidate includes the null cone.

The proof dependencies run from native multiplication and conjugation to the
regular-operator identities; from these to units/singularity; and from the
existing coordinate/duality equivalences to incidence. The full Clifford
noninjectivity result is a separate dimension argument. Neither geometric
analogy nor the requested determinant formula is used as an unproved edge.

## Explicit scope boundaries

No new octonion carrier, no associative ring instance on it, no complex scalar
unit, no new Clifford quotient or faithful full-Clifford embedding, no physical
momentum law, no affine normalization, no manifold/Grassmannian construction,
and no determinant fourth-power theorem was claimed by the initial contract.
The later exact determinant candidate is recorded below; its source review
does not establish kernel acceptance.
The native signature convention is the quadratic-square convention: four
positive and three negative imaginary generators. A scalar pairing on two
four-vectors does not make every full Zorn operator an imaginary Clifford
generator.

## Verification record

Initial disposition: **PENDING**. The source baseline is clean and matches the
published PR #437 tree. A nonblocking maintained-lock probe at
2026-11-24 08:48:16 UTC returned `BuildLockBusyError`; the external owner was
`shared-formalism:2`. No new Lake invocation has occurred at contract creation.
All nine pinned package HEADs, URLs, and clean working trees passed read-only
preflight; no packages are copied or changed. This is environment evidence,
not compilation or theorem acceptance.

Final source hashes, independent reviews, exact gate commands, actual compiler
and axiom-audit results, and any remaining blockage will be appended after
the candidate is fixed and checked.

### Exact determinant candidate added after the initial contract

The first two new owners passed independent source review and six static gates
in run-001. The exact determinant was initially separate proof debt. A complete
two-theorem candidate was then generated in an isolated file and independently
reviewed by `source_scout`. The native matrix signs and pinned matrix/determinant
API calls passed that source review. A required parser repair moved the scoped
heartbeat option before the theorem documentation comment; the mathematical
statement and proof body are unchanged. The repaired source was integrated as
`Lie/CanonicalZornRegularExactDet.lean`.

The scoped limit of 1,200,000 heartbeats is a bounded proposal, not a measured
runtime guarantee. All three new owners require fresh compilation and an axiom
audit. The expanded checker selects four owners with 27 public heads and ten
named upstream declarations: 37 expected records, zero observed at this point.
The determinant zero-set and incidence proofs remain independent of this new
finite determinant calculation.

### Independent run-002 source/static receipt

Disposition: **QA_BLOCKED for kernel acceptance; source/static checks PASS**.
The final frozen-snapshot comparison completed at 2026-11-24 09:12:31 UTC.
All eight staged files, the unchanged Clifford boundary owner, and all
control files matched the reviewed snapshot and index. There were no
unstaged differences. The three new owners contain 22 theorem candidates
with complete proof bodies and one linear-equivalence definition.

- Independent mathematical/source review: PASS for all three new owners.
- Six static gates: all exit 0 across all four selected owners.
- Forbidden proof constructs, vacuity warnings, semantic-content findings,
  and OpenGauss findings: all zero in the selected sources.
- Independent inventory: 9 + 12 + 2 + 4 = 27 owner heads, plus ten reused
  declarations; 37 expected axiom records and zero observed records.
- Workflow delta: only the exact-determinant trigger path was added. Every
  executable block is byte-identical to the run-001 syntax-checked version.
  That earlier review passed YAML parsing, five shell syntax checks, and
  two embedded Python syntax checks. No actionlint result is claimed.
- Verifier delta: one target and the corresponding docstring count; existing
  gate semantics and the reused verifier defaults are unchanged.
- Fresh Lean elaborations, Lake invocations, axiom checks, and root integration:
  zero in both local QA runs. No compiler was queued or launched.

Run-001 recorded an active external shared-lock holder at 09:04:31 UTC
(`legendre-incidence:2`). Run-002 did not repeat that probe or infer that the
same holder remained active. This is a local validation blockage, not a
proof failure and not theorem acceptance. The GitHub workflow will provide
the next actual compiler evidence for the published revision.

Exact static commands (repository-root working directory):

```bash
python3 tools/quality/proof_proxy_staged_gate.py --strict lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean
python3 tools/quality/semantic_vacuity_gate.py lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --fail-on error --json-out /tmp/real-dirac-publication-recovery/zorn-intake/qa/run-002/semantic-vacuity.json
python3 tools/quality/semantic_content_audit.py --file-prefix lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean --file-prefix lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean --file-prefix lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean --file-prefix lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --gate --json-out /tmp/real-dirac-publication-recovery/zorn-intake/qa/run-002/semantic-content.json --md-out /tmp/real-dirac-publication-recovery/zorn-intake/qa/run-002/semantic-content.md
python3 tools/infra/opengauss_screener.py lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --strict --json
python3 tools/infra/opengauss_cli.py refute lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --strict --json
python3 tools/infra/opengauss_cli.py review lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean lean/InfoGeometry/Lie/SplitOctonionCliffordNoninjective.lean --gate GATE_4 --json
```

Frozen implementation hashes:

| Path | SHA-256 |
| --- | --- |
| `lean/InfoGeometry/Lie/CanonicalZornRegularNorm.lean` | `3140b8ff4a9f4c9673596e558ea082622c5be70d2c980a723827b161349662f5` |
| `lean/InfoGeometry/Lie/CanonicalZornWittRegularBridge.lean` | `5e0f52cd147dc72b9987349ea26234a6bfb5658027fdbe9327880e761eab2d76` |
| `lean/InfoGeometry/Lie/CanonicalZornRegularExactDet.lean` | `8320933207fc0c8607fc3f5b411d5852681798355527ded68afe3a1cef7c1167` |
| `verification/zorn-witt-regular/check.py` | `4f188ad61f52c45428e3c9a263915f89c6af24ef8442a0dfbc2995c2b28e0c84` |
| `.github/workflows/zorn-witt-regular.yml` | `946840adb9cb136173967920f36c1a6a952fdd923f65d6930d2a665da03e461d` |

Evidence receipt hashes (local independent QA, not compiler evidence):

| Receipt | SHA-256 |
| --- | --- |
| `run-002/static-gate-receipts.json` | `fa4e1d173b0390edc8e581e960ea7318f90b5fc18ec2e74c26b46432ed167764` |
| `run-002/independent-inventory.json` | `792fefcd51c3e21c3d9c5127a59d470663c5d3f268e2b89170e53168575a5dae` |
| `run-002/delta-review.json` | `1f252ba0fb4296c848f7aa7c8619265bc18d96ee3a88a342c2f7e4fdbaa131c6` |
| `run-002/final-inspection.json` | `20e15a6ac202ef2643d158c17d650ed8e11950138ae622f5c39f905fa0149afd` |

The raw attachment remains byte-identical at 22,525 bytes. No dependency
pin, gate implementation, existing source owner, package source, or shared
cache was changed by this packet. Publication for review does not establish
kernel acceptance, root integration, or merge readiness.
