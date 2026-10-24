# Branch consolidation audit

## Current inventory: 2026-10-23

`git fetch upstream` completed. Two successful `git ls-remote --heads upstream`
reads returned **20 live heads: main and the 19 topic heads below**. Remote main
was `21189e55133ed207043f2f05e37aa52d1fc8a9f5`. Local stale remote-tracking
`codex/*` and PR refs are not additional live branches. No branches were deleted.
This supersedes the previous undated 180-head inventory and its blanket
statement that no branch-only content was promoted.

Comparison base for this inventory: local `977d5c2bd0e343fe1a5dc9d32aae4c3dab72c316`.
“Changed Lean paths” compares source paths under `lean/` in each branch with
its merge base against local HEAD. “Absent paths” counts `lean/**/*.lean` branch
files whose exact path is absent from HEAD;
it does **not** count missing mathematics. Renamed owners, native replacements,
and deliberately omitted forwarding modules require declaration-level review.
Dirty worktree additions are not counted as committed consolidation.

| Live topic branch | Exact head | Changed Lean paths | Absent paths |
| --- | --- | ---: | ---: |
| `feat/attention-analogy-fibers` | `c2793aec5b388c254de8b8a3adc9d3a31e39d7b0` | 5 | 0 |
| `feat/attention-identifiability` | `c8960e2893dd8f0477e090ba3b6fb14269f40b74` | 7 | 0 |
| `feat/attention-polytope-decomposition` | `934feb8b0e6d55d461605abd742a3ce7d9dbcaa6` | 0 | 0 |
| `feat/attention-value-geometry` | `9d3a7c721f2d6f021a8009e461f8181cc67172d1` | 3 | 0 |
| `feat/block-causal-sinkhorn-contract` | `a80e22866f009e12bd13915463c2a8031eae9220` | 4 | 0 |
| `feat/car-majorana-pfaffian-bridge` | `eaa2efff0f476d7da62ed3df49b0df63df957391` | 4 | 1 |
| `feat/cartan-drazin-mp-cycle` | `6a2dd21237e949f8fb8ffc75bf90e996e0cb65c2` | 3 | 3 |
| `feat/causal-bipartite-sinkhorn` | `55fac9ffc20509124192529060d158178126801d` | 14 | 0 |
| `feat/drazin-mp-sector-partitions` | `261ca866ac6c8f90bdb64fbbb3908e49ba81029f` | 6 | 3 |
| `feat/drazin-shell-cascade` | `096537815fc734b462f7a69af6394af79d3c3c4b` | 11 | 6 |
| `feat/drazin-shell-resolution` | `97fb2a606362bc09fa1f6681baa9d7b68c9599a0` | 10 | 6 |
| `feat/functional-route-certificates` | `4b278639fa013a88b67a2565cdeb1564cf70418d` | 3 | 0 |
| `feat/functional-route-fiber-diagnostics` | `b8f4038cccd18dc3eb1cf8023cdbfe4dddc178f7` | 2 | 0 |
| `feat/mass-spec-multienergy-identifiability` | `4ea2c6f5429a23cb57a751a34296a22881afc684` | 0 | 0 |
| `feat/peirce-square-zero-mp` | `5e4435976cc4ffb1b75dd46460dc7ec2c8a7a375` | 15 | 9 |
| `feat/pruning-gramian-shape-sinkhorn` | `08f251a4b2c18eac4f20d68a30a2c3610390c9ce` | 12 | 0 |
| `feat/supercolor-source-closure` | `41284b6c0a84785c7bf20ed153a0c17b29f98932` | 3 | 0 |
| `feature/thermal-clifford-parakahler-bridge-20261020` | `404368f0c6b4cf006ae9cceb35211459839336ee` | 3 | 0 |
| `fix/main-verification-bootstrap-20261023` | `81867ee217620005c5c18c4cb78b15f8d24f68db` | 0 | 0 |

## Acceptance boundary

Current main contains owner-level repairs and integrations beyond these branch
snapshots. Do not overwrite them with stale branch files merely because a diff
exists. The current review traces CAR/Majorana/Pfaffian, supercolor, Cartan, and
Drazin declarations to their actual owners before further promotion.

The reviewed-owner verifier repair at `977d5c2bd` passed independent source
review and component QA: 26 Python tests; native Lean 4.34.1 positive owner
coverage including private bodies and quoted module names; rejection of an
import-only selected target, unsafe declaration, and custom axiom dependency.
The four verified source hashes are recorded in the independent QA receipt at
`/tmp/reviewed-audit-fixed-independent-qa-7gx1z1di/status.json` and its sibling
`hashes-after.json`. These temporary receipts describe this local run; they are
not a durable or reproducible full-union acceptance claim.

The 65-target native verification lane remains incomplete. It must preserve all
nine October additions, resolve the real Architect dependency, and establish
pinned package provenance. Component audit-generator success does not imply
full-union, full-library, runtime, or clean-dependency acceptance. Aggregate
changes and foreign drafts still need their own source-stable verification.
No new push or completion of consolidation is asserted by this inventory.

## Revalidation: 2026-10-24, local `9676676663a6211d10277708fa531976019d6d87`

A fresh `git fetch upstream` and `git ls-remote --heads upstream` succeeded.
The live set is still exactly main plus the nineteen topic heads listed above;
all twenty hashes are unchanged. Recomputing branch-only Lean paths against
this local commit gives the same absent-path lists/counts. This is an inventory
result, not a claim that every branch theorem has been consolidated.

The absent `Canonical/MajoranaLinearKernel.lean` was read at branch
`eaa2efff0f476d7da62ed3df49b0df63df957391`. Its coefficient carrier and
quadratic normalization agree with the current native implementation:

| Branch construction/result | Current owner or primitive |
| --- | --- |
| `field`, `field_zero`, `field_single` | Mathlib `Fintype.linearCombination`, its linear-map zero law and `linearCombination_apply_single` |
| coefficient extraction and injectivity | `MajoranaCoefficientAction.linearCombination_anticommutator`, `linearCombination_injective` |
| bilinear contraction | `MajoranaCoefficientAction.quadratic_monomial_commutator` |
| normalized quadratic operator and its generator/span actions | `quadraticElement`, `quadraticElement_commutator_generator`, `quadraticElement_commutator_linearCombination` |
| zero commutator iff coefficient kernel | `MajoranaCoefficientAction.quadraticElement_commutator_eq_zero_iff` |
| Pfaffian kernel and conserved nonzero Majorana | both theorems in `MajoranaPfaffianKernelCriterion` |
| finite-chain endpoint consequence | `CARMajoranaOwnerAdapters.sweetSpot_boundary_commutes` |

The branch's general finite-bilinear sum statement is more general in its
indexing than the named chain endpoint theorem. Its constituent proof is
available from `KitaevChainMajoranaZeroModes.left_boundary_majorana_zero_mode`,
`Commute.mul_right`, and `Commute.sum_right`; a named general-sum owner theorem
has not been established by this bounded comparison. This distinction prevents
an exact-name or special-case coverage claim from substituting for consolidation.
No stale branch carrier or forwarding module was copied into main.

### Cartan and square-zero Peirce declaration review

An independent read-only review compared the fetched Cartan head `6a2dd21237e9`
and Peirce head `5e4435976cc4` against `9676676663a6`. It did not establish a
missing mathematical consequence in those two reviewed areas:

- `Algebra/PeirceParityClosure.lean` supplies parity projection laws,
  decomposition uniqueness, product laws, conjugation equivalence, and sign
  converses retaining injective doubling.
- `Core/PeirceGrading.lean` supplies actual complementary submodules,
  reflection, odd reconstruction, and square-zero directed corners.
- `Core/NilpotentToCartanDrazinMPPoset.lean` supplies support idempotence under
  the weaker inner-inverse condition and orthogonal-difference powers.
- `Canonical/DrazinPeirceParity.lean` supplies operator/inverse/nilpotent parity
  and anomaly recovery, including the negative left-defect sign.
- `Singular/SquareZeroMoorePenrose.lean`, `MoorePenroseChiralDefects.lean`, and
  `Core/JordanAssociatorRing.lean` cover inverse square-zero, harmonic support,
  overlap criteria, common squares, and the unnormalized associator.
- Native shell-resolution/extinction/action owners and the oblique-shell and
  characteristic-two regression owners preserve the relevant boundary cases.

This is source comparison, not a new kernel acceptance run or proof that every
inherited shell API spelling is present. In particular, real-matrix column
wrappers must not be advertised as arbitrary-star-ring column APIs. The
exact/coexact/harmonic split must not be confused with the two-block split at
`p,1-p`; general harmonic cross terms remain necessary. No existence of a
Moore–Penrose inverse follows from the conditional support theorems.

### General finite-bilinear consequence closed

The historical missing-name qualification above is now resolved by the native
`KitaevChainMajoranaZeroModes.boundary_commutes_finite_bilinear_sum`. It works
in any ring over an arbitrary finite set, with varying coefficients commuting
only with the boundary element. Local anticommutation with each bond factor
suffices. Taking the full finite index set, constant coefficient, and the
branch CAR/index-inequality premises recovers the branch consequence.

Independent source A-A passed. Independent QA built the owner, audited its
axioms, and rebuilt `OperatorAlgebra.All`, all with exit zero and stable
captured sources/pins. Receipt:
`/tmp/qa-a-kitaev-boundary-qprmk6aj/result.json`.
Owner SHA-256: `c66ec2bad14ef2a6ade7fc4710e7b401731245f108f8c171fe1d472795ac4468`.
This closes this branch consequence, not the remaining repository-wide gates.
