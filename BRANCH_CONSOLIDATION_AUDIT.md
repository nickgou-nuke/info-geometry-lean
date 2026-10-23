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
