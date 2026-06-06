# Media Recovery Ledger - 2026-06-06

This ledger records the recovery pass over the `/media` archives and the
repo-native disposition of each useful idea.  It is deliberately conservative:
Lean source in this repository is proof authority; archive files, SymPy output,
Arango records, GraphRAG hits, and chatbot reviews are navigation evidence only.

## Source Roots

Scanned roots:

- `/media/goutev/SP DS72/auto/proofs`
- `/media/goutev/SP DS72/auto-archive/cocycle_complex_core_20260605`
- `/media/goutev/SP DS72/cocycle_complex_20260605_2138/tmp/cocycle_archive_proofs`

The scan included Lean files, proof-plan markdown, architecture notes, and the
core knowledge-base sidecar where present.

## Recovery Rule

Do not copy whole archive modules into the repo unless they are already clean
owner files.  Most archive modules mix useful finite lemmas with `True :=
trivial`, `sorry`, `#check`, prose-only theorem names, or standalone namespace
surfaces that duplicate existing owners.

The accepted route is:

1. Identify the existing owner file in `lean/InfoGeometry`.
2. Extract only kernel-useful finite lemmas or definitions.
3. Rename examples into public theorem names when appropriate.
4. Build the touched owner module.
5. Record unported material as debt, not as proof.

## Recovered In This Pass

| Archive source | Repo owner | Result |
| --- | --- | --- |
| `/media/goutev/SP DS72/cocycle_complex_20260605_2138/tmp/cocycle_archive_proofs/tri_factor_sl2r.lean` | `lean/InfoGeometry/Dynamics/KanDecomposition.lean` | Ported the determinant-one KAN facts into the existing complex KAN owner as named theorems: `componentK_det_eq_one`, `componentA_det_eq_one`, `componentN_det_eq_one`, `kanProduct_det_eq_one`. |
| `/media/goutev/SP DS72/cocycle_complex_20260605_2138/tmp/cocycle_archive_proofs/monodromy_cocycle.lean` | `lean/InfoGeometry/Topological/FibonacciAnyons.lean` | Ported the diagonal `R` cancellation as generic finite theorems: `R_dual_matrixOf`, `R_matrixOf_mul_R_dual_matrixOf`, `R_dual_matrixOf_mul_R_matrixOf`. |
| `/media/goutev/SP DS72/cocycle_complex_20260605_2138/tmp/cocycle_archive_proofs/zorn_cubic.lean` | `lean/InfoGeometry/Canonical/TriFacetGeometry.lean`, `lean/InfoGeometry/Canonical/TriFacetComplete.lean`, `lean/InfoGeometry/Canonical/FibonacciParafermionAtoms.lean` | Not copied.  The repo already has stronger tripotent projector algebra.  Cleaned the old bucket-style header in `TriFacetGeometry.lean` and narrowed unused assumptions on theorems that do not need `Invertible 2`. |
| `/media/.../legendre_final.lean` | `lean/InfoGeometry/Canonical/LieFenchelQuadratic.lean`, `lean/InfoGeometry/Convex/Legendre.lean`, `lean/InfoGeometry/Geometry/LegendreDuality.lean` | Not copied.  The archive complete-square proof is kernel-useful, but the repo already owns a stronger inner-product quadratic Fenchel/Bregman surface. |
| `/media/.../souriau_proof.lean` | `lean/InfoGeometry/Canonical/SouriauFenchelOnsagerBridge.lean`, `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean` | Not copied.  The integer cocycle demo is useful as a sanity check, but the repo already owns the explicit affine coadjoint/Fenchel gap invariance interface. |
| `/media/.../connes_simple.lean`, `/media/.../connes_mellin.lean` | `lean/InfoGeometry/Dynamics/TomitaTakesaki.lean`, `lean/InfoGeometry/Canonical/RelationalInformationDynamics.lean` | Not copied.  These are scalar exponential shadows of modular cocycle language; keep them as examples unless a named scalar Connes sidecar is needed. |

Validation for the KAN and diagonal `R` recovery:

```text
lake env lean lean/InfoGeometry/Dynamics/KanDecomposition.lean
lake build InfoGeometry.Dynamics.KanDecomposition
lake env lean lean/InfoGeometry/Topological/FibonacciAnyons.lean
lake build InfoGeometry.Topological.FibonacciAnyons
lake env lean lean/InfoGeometry/Canonical/TriFacetGeometry.lean
lake build InfoGeometry.Canonical.TriFacetGeometry
```

Both commands passed.  The Lake build emitted only pre-existing linter warnings
from `lean/InfoGeometry/Algebra/HypercomplexTriad.lean`.

## Archive Classification

| File or group | Classification | Disposition |
| --- | --- | --- |
| `FibAnyonThm1.lean`, `FibAnyonThm2.lean`, `FibAnyonThm3.lean`, `fibanyon_thm1_fusion.lean`, `fibanyon_thm2_fmatrix.lean`, `fibanyon_thm3_rmatrix.lean` | Finite matrix facts, partly useful. | Do not copy over the categorical surface.  Compare only against `lean/InfoGeometry/Categorical/FibonacciBraiding.lean`, `lean/InfoGeometry/Categorical/FibonacciFusionCategoryData.lean`, and finite Fibonacci owner files. |
| `fibanyon_thm4_yangbaxter.lean`, `fibanyon_thm5_braidgroup.lean`, `FibAnyonThm4.lean`, `FibAnyonThm5.lean`, `HexagonCocycle.lean`, `fib_category.lean` | Mixed finite facts and placeholder theorem surfaces. | Keep as search hints only.  `True := trivial` hexagon/Yang-Baxter claims are not proof. |
| `hexagon_proper.lean` | Potentially valuable but not trusted. | Candidate for oracle-assisted repair only after sending the full file plus current build errors and requesting one complete drop-in replacement. |
| `monodromy_cocycle.lean` | Small kernel-useful diagonal phase inverse identities. | Ported generically to `Topological/FibonacciAnyons.lean`; no hard-coded exponential phase was copied. |
| `fibonacci_v4.lean` | Mostly finite golden-ratio and `ZMod 2 x ZMod 2` labels. | Superseded by `lean/InfoGeometry/Canonical/V4SemidirectS3Bridge.lean`, `lean/InfoGeometry/Canonical/Cl55V4SpinorFragmentation.lean`, and `lean/InfoGeometry/Canonical/TrialitySpin8Permutations.lean`. |
| `bdg_kan.lean` | Placeholder bridge surface. | Do not import.  Use `lean/InfoGeometry/Canonical/RealBdGNambuGorkovFusion.lean`, `lean/InfoGeometry/OperatorAlgebra/AndreevBoundary.lean`, and `lean/InfoGeometry/Physics/FermionicAndreevReflection.lean` instead. |
| `e11_colimit.lean` | Useful `An` matrix shape plus placeholder colimit claims. | Matrix shape may be ported later if an owner needs it; colimit claims are not proof. |
| `triality_braiding.lean` | Useful cube-root scalar identities plus `True` bridge claim. | Do not import the bridge.  Compare scalar identities against triality owner files if needed. |
| `zorn_cubic.lean` | Useful finite cubic/tripotent algebra plus placeholder tri-factor claim. | Superseded by stronger tripotent projector owners; no archive code copied. |
| `formal-theory*.lean` | Contains `sorry` and theorem-shaped prose placeholders. | Quarantine as prose translation input only. |

## Owner Surfaces To Prefer

- Categorical Fibonacci: `lean/InfoGeometry/Categorical/FibonacciBraiding.lean`
- Fibonacci fusion data: `lean/InfoGeometry/Categorical/FibonacciFusionCategoryData.lean`
- Tensor tower colimits: `lean/InfoGeometry/Canonical/TensorTowerColimit.lean`
- Universal Grothendieck layer: `lean/InfoGeometry/Algebra/Grothendieck.lean`
- KAN component algebra: `lean/InfoGeometry/Dynamics/KanDecomposition.lean`
- Hyperbolic real KAN shadow: `lean/InfoGeometry/Dynamics/HyperbolicComponent.lean`
- Finite Souriau/Fenchel/Onsager: `lean/InfoGeometry/Canonical/SouriauFenchelOnsagerBridge.lean`
- Smooth Legendre inverse: `lean/InfoGeometry/Geometry/LegendreHessianInverse.lean`
- V4/Weyl/triality: `lean/InfoGeometry/Canonical/V4SemidirectS3Bridge.lean`,
  `lean/InfoGeometry/Canonical/Cl55V4SpinorFragmentation.lean`,
  `lean/InfoGeometry/Canonical/TrialitySpin8Permutations.lean`
- Andreev/BdG/Krein: `lean/InfoGeometry/OperatorAlgebra/AndreevBoundary.lean`,
  `lean/InfoGeometry/Physics/FermionicAndreevReflection.lean`,
  `lean/InfoGeometry/Canonical/KreinMajoranaZeroModeBlock.lean`
- Noncommutative projective defect: `lean/InfoGeometry/Projective/NoncommutativeCrossRatio.lean`

## Oracle Use Policy

Use aiClaw/ChatGPT only for hard Lean repair, not for importing prose.

Required prompt shape:

```text
TASK: Return one complete Lean 4 file as a drop-in replacement.
CONSTRAINTS: no sorry, no admit, no axioms, no placeholder theorem surfaces,
no prose buckets, no patch fragments.
INPUTS:
1. Complete current Lean file.
2. Complete build command.
3. Complete build errors.
OUTPUT:
Exactly one fenced lean4 code block containing the full replacement file.
```

Submit one complete prompt, wait for the final answer, then apply and test in
one pass.  Do not send serial partial prompts into the same chat window.

2026-06-06 status for `hexagon_proper.lean`: isolated Lean checking found real
errors, but the live ChatGPT tab was already serving unrelated prompts from
other senders.  No hexagon response from that contaminated tab was accepted as
evidence.  Retry only after the queue and DOM preflight both show a clean,
idle lane.

## Remaining High-Value Recovery Targets

1. Attempt `hexagon_proper.lean` in isolation.  If it fails nontrivially, route
   the full file and errors through the oracle using the drop-in protocol above.
2. Audit untracked Fibonacci/V4 modules in the repo for placeholder theorem
   surfaces and either replace them with imports from owner files or leave them
   unpromoted.
