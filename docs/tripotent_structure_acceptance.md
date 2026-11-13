# Tripotent structure: scoped kernel acceptance

The ten mathematical modules in PR #352 have independent source-semantic and
execution-QA acceptance. Their exact closure of **58 repository modules**
compiled in two separate fresh CI runs. Each native ownership-based audit
checked **157 declarations**, covering all ten owners and their **101 named
source theorems** (including four private theorems). The observed axiom union
is exactly `propext`, `Classical.choice`, and `Quot.sound`.

This record certifies the selected mathematical source. Repository-wide build
and merge acceptance remain separate; the root-build boundary is below.

## Exact checked sources

| Item | First execution | Second execution |
|---|---|---|
| Published source | `7dda7101e3340adab4bf85d535895b445854e3ea` | `337d7ef1c9433d342e92ead649f95b6e2481780a` |
| Tested merge | `4199341fb43a758fde569b72fe0e1b9fa9cd9f58` | `38aece91848c1654e7a8f4a0612de8c2d05ce533` |
| Source tree | `bb9f7fb6180b53cf92ce433386f9781f2c95c18b` | `d51c5028909b7bc77706cf7ae31474fc78af1130` |
| Successful kernel job | [131831152975](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43409179642/job/131831152975) | [131838779166](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43409480149/job/131838779166) |
| Compilation | 58/58 | 58/58 |
| Owned declarations audited | 157 | 157 |

All 58 proof-source hashes are identical between these checkpoints. The sole
intervening change installs and verifies `ripgrep` before the source/root
gates. The focused kernel job, native checker files, Lean pin
`leanprover/lean4:v4.34.1`, and Mathlib pin
`d13f23b723b8a846827a245b89c10fc7d3f11612` are unchanged. These were two separate
workflow runs, not a manually requested job rerun.

Independent QA checked both downloaded artifacts against the frozen Git-blob
snapshots, all copied source hashes, the actual Lean version, the generated
native audit program, every declaration record, and the immutable tested
commit/tree identities. The two native audit logs and all 58 module-log
hashes are byte-identical.

## Mathematical scope

The carrier is an arbitrary unital associative real algebra. The construction
retains its ordered multiplication and uses the existing adjoint eigenspaces
`adGrade S k`. From `S * S * S = S`, it constructs a native `GradedAlgebra`,
an internal integer direct sum, and an `AlgEquiv` from the external direct sum
to the original algebra. The support is contained in `[-2, 2]`.

The remaining owners prove the typed integer super-Jacobi identity;
Lagrange-projector restriction to invariant submodules and Lie subalgebras;
strict and normalized dual-kernel formulas for actual `Module.End` actions;
the extreme Jordan pair with separate linearity laws; ordinary and Krein
involution criteria; finite-sum odd-corner generation; and grade transport
and composite centralization. The adjoint defect is

$$D^4-D^2=12(\Pi_2+\Pi_{-2}).$$

The [theorem contract](tripotent_krein_morita_contract.md) gives the exact
owner/dependency map, hypotheses, corrections to the intake, and remaining
analytic boundary. In particular, the quintic is an annihilator, some grades
may vanish, the corner-span result is not global Morita equivalence, and no
unbounded Stone/Tomita/KMS construction is asserted.

## Preserved evidence

The compact evidence directory contains the original independent review and
repair reviews, both source snapshots, both parsed checker statuses, both
complete declaration-audit records, immutable remote metadata, the final QA
record, and the independently reviewed artifact verifier:

- [Final mathematical-source acceptance](verification/tripotent_structure/qa-a-acceptance-337d7ef1.json).
- [Exact preservation manifest](verification/tripotent_structure/qa-a-preservation-manifest.json).
- [Checksums](verification/tripotent_structure/qa-a-preservation-SHA256SUMS).
- [Artifact verifier](verification/tripotent_structure/verify_tripotent_remote_artifact.py).

The acceptance-record SHA-256 is
`929485ee8dec3ee33270e939f3c28f6b1c0fd7fe3c401ebbac2b65a8ededcf6b`.
The preservation-manifest SHA-256 is
`b386c0d5533c870dfe145199dc8cffeb8505948e6ca7a3062c73f349d30931a3`.
Bulky archives and full job logs are represented by their immutable run/job
references and recorded hashes. Every listed evidence file is retained byte-for-byte.

To check the preserved files, run
`sha256sum -c qa-a-preservation-SHA256SUMS` from the evidence directory. To recheck a
downloaded workflow artifact and its decoded job log:

```bash
python3 docs/verification/tripotent_structure/verify_tripotent_remote_artifact.py \
  --snapshot docs/verification/tripotent_structure/qa-a-source-snapshot-337d7ef1.json \
  --artifact-root /path/to/extracted-artifact \
  --job-log /path/to/kernel-job.log \
  --repository . \
  --output /path/to/artifact-verification.json
```

The artifact directory must contain `status.json`, `audit.log`,
`lean-version.txt`, the module logs, and `src`. This verifier checks existing
evidence; it does not invoke Lean. It explicitly rejects optimized Python,
binds all four native checker/generator files to the reviewed hashes before
using the generator, and compares the actual Lean version to the pin.
The separate immutable GitHub commit/tree correspondence is preserved in the
remote-evidence record; it is not inferred from an artifact's own claims.

## Repository integration boundary

The completed first successful run passed the actual nonempty staged proof
gate on exactly the ten owner paths. Its unchanged incremental and explicit
full root builds failed at the absent local dependency
`external_refs/homotopy-hypothesis-lean4`. Its earlier Theory Audit emitted
missing-`rg` errors despite a successful wrapper exit; that scan was not
accepted as substantive execution.

At the final QA observation, **2026-11-13 10:55:37 UTC**, the second run's
prerequisite step (including `rg --version`) and staged proof gate had passed,
the incremental root gate had failed, and the full root gate remained in
progress. The record does not infer a cause for that latest failure or claim
that the full check completed. Its subsequent state is available in
[run 43409480149](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43409480149).

This documentation/evidence preservation does not change the accepted Lean
sources, checker files, workflow, or dependency pins. PR #352 remains stacked
on #323's `feat/tripotent-graded-operator-flow` branch at
`c23aa651772224079271a35a0acca5a3f9767354`; no merge acceptance is implied.
