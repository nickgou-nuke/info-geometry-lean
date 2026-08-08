# External `auto` ahead-commits audit — 2026-06-20

Scope: the two commits by which `/home/goutev/repos/info-geometry-lean/external_refs/auto` is ahead of its stale `origin/main`.

## Commit facts

- External branch HEAD: `1ab19d5152112a6d17f161dcbc8a361c15af3170`
- External branch comparison base (`external_refs/auto` `origin/main`): `9a191b0c98afdc3a28873ce5d5ef5c106ba6b194`
- Ahead commits:
  - `1ab19d5 Merge preserved local auto edits onto origin main`
  - `64cc948 WIP preserve local auto external-ref edits before origin sync`
- Current `/home/goutev/auto` HEAD while auditing: `2332a44fb68e56ec69f39584bc073d6dc8d43802`

## Verdict

The ahead-commit code is not lost. Of the 18 committed paths changed by the external ahead commits, 14 are byte-identical in current main. The remaining 4 are intentionally different because current main is newer: `BraidCliffordIntegration.lean` contains the external material plus the later Majorana finite certificate strengthening, `LieFlowMatching.lean` has theorem-honesty wording tightened, `proofs/lakefile.toml` has all external ahead roots plus hundreds of newer roots, and `README.md` has the newer project manifest/licensing/citation text.

No wrapper/socket replacement was accepted as a substitute for code: the relevant external Lean/Python repairs are already active in current main, and the full project was built successfully after integration in the prior no-loss pass.

## File-by-file comparison

| path | status vs current main | external HEAD SHA256 | current SHA256 | diff shortstat |
|---|---|---:|---:|---|
| `proofs/BraidCliffordIntegration.lean` | different | `f498a9fac599a183` | `761fc5651d64a753` | 1 file changed, 244 insertions(+), 1 deletion(-) |
| `proofs/CuntzKTheoryPairing.lean` | identical | `5e7d4635c40e0b8a` | `5e7d4635c40e0b8a` |  |
| `proofs/CuntzKTheoryPairing.py` | identical | `927202703e78d84e` | `927202703e78d84e` |  |
| `proofs/FibonacciCliffordBridge.lean` | identical | `72dca3c9f4d45301` | `72dca3c9f4d45301` |  |
| `proofs/GT_FromText.lean` | identical | `c1848c6d10c59988` | `c1848c6d10c59988` |  |
| `proofs/HilbertPolyaBivariant.lean` | identical | `558fe14ff1303af4` | `558fe14ff1303af4` |  |
| `proofs/KanCayley.lean` | identical | `72ba722007faeb6d` | `72ba722007faeb6d` |  |
| `proofs/KasparovKreinCategory.lean` | identical | `25feb16d308501bc` | `25feb16d308501bc` |  |
| `proofs/KasparovKreinCategory.py` | identical | `b4e083fc346c9584` | `b4e083fc346c9584` |  |
| `proofs/KreinVacuumKMSBridge.lean` | identical | `9b7b578292b38cde` | `9b7b578292b38cde` |  |
| `proofs/LieFlowCompilerBridge.lean` | identical | `c1f4b7b92940a724` | `c1f4b7b92940a724` |  |
| `proofs/LieFlowMatching.lean` | different | `edc0f5c7a94f8dfa` | `6699b4ae76ff0dbe` | 1 file changed, 2 insertions(+), 2 deletions(-) |
| `proofs/lakefile.toml` | different | `6448b010ae3ebc29` | `14b255547b73c52b` | 1 file changed, 366 insertions(+), 83 deletions(-) |
| `proofs/test_simp.lean` | identical | `62d3587028bca4ef` | `62d3587028bca4ef` |  |
| `proofs/tomita_kms_v4.lean` | identical | `e002a6963b5c2c99` | `e002a6963b5c2c99` |  |
| `proofs/tomita_kms_v4.py` | identical | `15fa8d2dbeb9e56e` | `15fa8d2dbeb9e56e` |  |

## Non-identical path notes

- `proofs/BraidCliffordIntegration.lean`: current main is a strict later integration over the external ahead version. It includes the external braid/Clifford finite algebra plus imported `MajoranaBraidGroup` gates and proved Artin/noncommutation strengthening.
- `proofs/LieFlowMatching.lean`: current main only changes wording from “axioms” to “explicit field identities”; this is the theorem-honest version.
- `proofs/lakefile.toml`: current main includes all external ahead roots plus newer integrated roots. The scratch/test roots `CheckLimit`, `CheckPUnitAdd`, `TestAF`, `test_ring`, and `test_simp` were also restored as Lake roots and build successfully.
- `README.md`: current main has the newer public project manifest, verification instructions, authorship/license/citation section; the external ahead README is older.
