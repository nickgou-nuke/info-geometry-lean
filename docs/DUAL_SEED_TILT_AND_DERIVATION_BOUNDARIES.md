# Additive tilt, inner shift, and their precise boundaries

## Intake and theorem contract

This continuation of PR #304 starts from commit
`5a19e9da359692a14f6682b8588b3a0e591c9747`. Its inputs are the 2026-11-10
conversation's additive tilt / exponential shift proposal and the complete
attachment `Pasted text(20261110-104657).txt`, SHA256
`1e2f85d4c4763b909b2a64bc2e65c48be9c2f933c7f2a86babaa12a7c203a6b9`.
The attachment additionally proposes Souriau, coadjoint, Dirac, Hodge,
Majorana, braiding, and Cantor interpretations. The source remains preserved;
this document records the mathematical claims extracted from it.

The ambient object is an associative, potentially noncommutative algebra
`A`. The existing `IsDualSeedPair d b` supplies `d*d = b*b = 0`,
`d*b*d = d`, and `b*d*b = b`. Write `H = d*b - b*d` and
`P0 = Subalgebra.centralizer K {d,b}`. **`P0` is a subalgebra, not a
distinguished element.** Additive tilt requires an explicit `z ∈ P0`:

\[
d_\varepsilon=d+\varepsilon z,\qquad
b_\varepsilon=b-\varepsilon z.
\]

The theorem surface uses native `Subalgebra.centralizer`,
`Commute`, scalar multiplication, `Module.End`, `LinearMap.mulLeft`,
`LinearMap.mulRight`, and the existing `splitCartanHom`. No replacement
algebra, changed multiplication, state, measure, or graded differential is
introduced by these definitions.

### Verified theorem scope

1. Over a commutative coefficient ring, compute both tilted squares, the
   anticommutator, the unchanged commutator `H`, and the affine Cartan weight
   equations. Retain every mixed term.
2. Over a coefficient field with `2 ≠ 0`, prove for `ε ≠ 0`:
   `C(d + ε • z, b - ε • z) = C(d,b) ⊓ C(z)`.
3. Characterize retention of the full normalized dual-seed equations by
   `ε • z = 0`. Square-zero alone is weaker than those four equations.
4. In the existing real Banach algebra, evaluate the actual exponential
   conjugation of the tilted seeds. Its zero-weight term is fixed and its
   seed terms carry weights `exp(2t)` and `exp(-2t)`.
5. On the native regular module, use left multiplication by a nonzero
   dual-seed pair and right multiplication by the same pair to prove a
   strict centralizer reduction and a nonzero tilted square. The right
   actions do not commute with each other; their multiplication order is
   reversed. Instantiate using the existing dense real matrix seed when
   appropriate, retaining the full endomorphism algebra.

These are algebraic theorems, except for item 4's actual Banach-algebra
exponential. Independent semantic review and kernel acceptance are recorded
below. Stronger narrative interpretations retain the ledger's separate scope.

## Source-grounded claim ledger

| Intake claim | Mathematical disposition / required structure |
| --- | --- |
| `P0` can be added to a generator | Requires choosing an element `z ∈ P0`; a subalgebra itself is not an algebra element. |
| Tilt breaks square-zero | Exact square formulas are the target. Nonvanishing needs hypotheses; a nonzero square-zero residual-corner perturbation can retain both squares. |
| Tilt preserves the original normalized pair | Target characterization: precisely `ε • z = 0` when `2 ≠ 0`. |
| Tilt changes the joint core | Exact intersection theorem above. Strictness requires a noncentral perturbation inside the original core. A central element of that core, including residual support, does not shrink it. |
| Exponential shift destroys nilpotency | False for an actual algebra automorphism. Existing `OperatorAlgebra.InnerConjugation` preserves nilpotency and its exact index. |
| These operations deform algebra multiplication | They change elements or act by an automorphism in the same algebra. A changed product needs a separate definition. |
| `[d,[z,b]]` generates a nonzero flow for `z ∈ P0` | It is zero because `[z,b]=0`. The existing nontrivial Cartan generator is `[d,b]`. |
| `d²=0` implies `ad(d)²=0` | False. `Core.LieJordanBoundaryOperators.ad_sq_of_sq_zero` gives `ad(d)²=-2 L_d R_d`. |
| The ordinary derivation anticommutator is the claimed simple wave operator | `Core.LieJordanBoundaryOperators.ad_mul_ad_add` retains a Jordan term and two sandwich terms. Coefficient derivatives also matter for compositions of coefficient-weighted derivations. |
| A square-zero graded differential follows | Existing `OperatorAlgebra.PeirceGradedSuperderivations` requires a specified grading involution and oddness. These are additional data. |
| The common commutant is automatically the entire Dirac kernel | Common commutation supplies annihilation in the proposed expression; the converse and a Hodge decomposition need separate proofs. |
| Cartan shift braids modes in the common commutant nontrivially | Existing `JointCentralizerDynamics.splitCartan_fixes_jointCentralizer` fixes them pointwise. A nontrivial braid requires different operators and proved braid relations. |
| Tilt and shift create Cantor cylinders | Existing Cantor owners supply product topology, prefix maps, and measures, but use different operations. An intertwining map from this additive tilt remains to be specified. |
| A logarithm of a Jacobian is itself an RN derivative | A positive density, its logarithm, and a generator are different objects. The measure/state and transport must be specified before identifying them. |
| A symplectic contraction follows from `i_X Ω = dS` | With a closed symplectic form this equation is Hamiltonian and gives `L_X Ω = 0`; dissipation requires additional data or a different equation. |
| `E² - 4 p1 p2` is the stated coadjoint Casimir | The sign depends on the stated bracket and dual-coordinate convention. With `[H,d]=2d`, `[H,b]=-2b`, `[d,b]=H`, ordinary dual coordinates, and `ad*(d)F=-F∘ad(d)`, one obtains `E'=2p1`, `p2'=-E`; the preserved quadratic expression has a plus sign. No coadjoint-orbit realization is claimed in this continuation. |
| Centrality implies entanglement, a spectral gap, or topological protection | These conclusions require a state, representation, spectrum, or a protected family and its stability theorem. They are not consequences of common commutation alone. |
| Berry curvature, a quantum group, or a braid representation is constructed | No parameter bundle, connection, quantum-group action, or braid representation is supplied by the additive formula alone. These remain separate construction targets. |

## Existing owner reuse and search scope

The bounded search covered the relevant repo-owned `Core`, `Algebra`,
`Canonical`, `OperatorAlgebra`, `Clifford`, and `Volume` modules, their imports
and relevant consumers, plus the pinned Mathlib declarations. Existing owners
are read as source; their filenames and historical build claims are not
validation evidence for this continuation.

- `Core/DualSeedCentralizer.lean`: native centralizer projection, naturality,
  bimodule laws, and common commutation with `H`.
- `Core/DualSeedCartan.lean`: actual Cartan weights and preservation of the
  seed equations by ring homomorphisms.
- `Canonical/JointCentralizerDynamics.lean`: native exponential, actual
  conjugation weights, and pointwise fixation of the common commutant.
- `Algebra/AssociativeRegularCommutant.lean`: left/right regular actions and
  the evaluation-at-one commutant theorem. The native Mathlib maps can be
  used directly without introducing a second representation API.
- `Canonical/Cl11LeftRightDoubleBridge.lean`: existing regular and finite
  tensor-tower realizations; a genuine noncommutative multiplicity corner.
- `Core/LieJordanBoundaryOperators.lean`: exact ordinary derivation squares
  and mixed compositions.
- `OperatorAlgebra/PeirceGradedSuperderivations.lean`: genuine graded
  Leibniz, square-zero, and paired-differential laws with explicit hypotheses.
- `Canonical/CelikKocakCantorOperators.lean`: sign multiplication and bit-flip
  operators; its `tilt` is not the additive tilt defined above.
- `Canonical/CuntzCantorBoundaryShift.lean` and
  `Canonical/CantorCylinderTopology.lean`: actual binary prefix dynamics and
  cylinder topology.
- `Canonical/CantorBernoulliL2OperatorTransport.lean`: actual measure transport
  for fair Bernoulli prefix maps. In particular the pushforward is twice
  the measure restricted to the chosen prefix branch. This needs no
  identification with the new algebraic perturbation.

The actual proof dependencies are:

- Seed relations and common commutation give the unchanged bracket and exact
  tilt defects. The Cartan weight equations recover the original generators,
  yielding the centralizer intersection.
- That intersection, together with noncommuting right actions, gives the
  strict regular-module witness. Together with the existing pointwise Cartan
  fixation, it gives fixation of the tilted common commutant.
- The existing exponential weights and fixation of `z` directly give the
  affine conjugation formulas for the tilted generators.

No edge to a Cantor/RN/Berry interpretation is asserted without its map.

## New declarations

| Owner | Principal declarations |
| --- | --- |
| `Core/DualSeedTilt.lean` | `phasePolarization_tilt`; `IsDualSeedPair.tilt_seed_sq`, `tilt_partner_sq`, `tilt_anticommutator`, `lie_phase_tilt_seed`, `lie_phase_tilt_partner`, `commute_tilt_iff`, `centralizer_tilt`, `isDualSeedPair_tilt_iff` |
| `Canonical/JointCentralizerTilt.lean` | `splitCartan_conjugates_tilt_seed`, `splitCartan_conjugates_tilt_partner`, `splitCartan_fixes_tilt_centralizer` |
| `Canonical/JointCentralizerTiltAudit.lean` | `regular_centralizer_tilt_lt`, `regular_tilt_sq_apply_partner`, `regular_tilt_sq_ne_zero`, `dense_regular_right_not_commute`, `dense_regular_tilt_centralizer_lt`, `dense_regular_tilt_sq_ne_zero` |

The concrete consumer is on
`Module.End ℝ (Matrix (Fin 3) (Fin 3) ℝ)`, not on the original matrix
centralizer. This is the full native regular endomorphism algebra. The
explicit right-action witness preserves `R(a)R(b)=R(ba)`.

## Validation

Independent semantic review passed for the complete implementation and the
subsequent explicit noncommutativity witness. Independent QA accepted the
selected theorem surface with limited scope: the algebraic/analytic theorems
above are checked; root-package integration and the ledger's additional
geometric/physical constructions remain separate obligations.

The exact environment is Lean **4.34.1**, with Mathlib pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

### Kernel and axiom checks

The first independent run rebuilt all **43 project modules**, without reuse,
and audited **94 declarations**. All eight selected PR modules had zero
warnings. Actual `lean -DwarningAsError=true` elaboration passed for all three
new owners. The static T16 check nevertheless rejected the audit file because
it did not expose a closed noncommutativity statement on the actual
endomorphism carrier.

The repair added only the twelve-line `dense_regular_right_not_commute`
theorem and docstring. It did not change any previous theorem, hypotheses,
proof, verification tool, or dependency. A separate independent semantic
review passed. Supplemental QA reused **42** modules only after validating
their source, dependency, toolchain, and compiled-artifact hashes; it rebuilt
the changed audit owner and repeated its actual Werror check. The full
declaration traversal was rerun for all eight targets, now **95 declarations**,
including private/generated helpers. The initial rejected receipt and all
its evidence are preserved separately from the successful supplement.

| Selected module | Audited declarations | Warnings |
| --- | ---: | ---: |
| `InfoGeometry.Core.DualSeedCentralizer` | 30 | 0 |
| `InfoGeometry.Canonical.JointCentralizerGeometry` | 14 | 0 |
| `InfoGeometry.Canonical.JointCentralizerGeometryAudit` | 2 | 0 |
| `InfoGeometry.Canonical.JointCentralizerDynamics` | 12 | 0 |
| `InfoGeometry.Canonical.JointCentralizerDynamicsAudit` | 5 | 0 |
| `InfoGeometry.Core.DualSeedTilt` | 21 | 0 |
| `InfoGeometry.Canonical.JointCentralizerTilt` | 4 | 0 |
| `InfoGeometry.Canonical.JointCentralizerTiltAudit` | 7 | 0 |

Only `propext`, `Classical.choice`, and `Quot.sound` occur in the audited
axiom closure. No custom axiom or proof-hole dependency was introduced.
The 41 warnings in unchanged imports are: `MoorePenrose` 14,
`PeirceDecomposition` 1, `JordanPeirceDecomposition` 2,
`JordanAssociator` 7, and `HestenesKreinOperatorCalculus` 17.

The decisive initial command, from the checkout root, was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root .lake/packages/mathlib \
  --lean /workspace/scratch/84e89547e5ac/runtime/lean-4.34.1-linux/bin/lean \
  --output /workspace/scratch/84e89547e5ac/info-geometry-lean/scratch/dual-seed-tilt-qa \
  --target InfoGeometry.Core.DualSeedCentralizer \
  --target InfoGeometry.Canonical.JointCentralizerGeometry \
  --target InfoGeometry.Canonical.JointCentralizerGeometryAudit \
  --target InfoGeometry.Canonical.JointCentralizerDynamics \
  --target InfoGeometry.Canonical.JointCentralizerDynamicsAudit \
  --target InfoGeometry.Core.DualSeedTilt \
  --target InfoGeometry.Canonical.JointCentralizerTilt \
  --target InfoGeometry.Canonical.JointCentralizerTiltAudit
```

The supplement used the same eight `--target` arguments, a separate
`scratch/dual-seed-tilt-qa-supplement` output, and `--incremental`; axiom
auditing remained enabled. The three Werror checks used the pinned `lean`
binary, the checker's recorded `LEAN_PATH`, and the copied exact sources,
under the shared build lock. The changed audit's Werror check was repeated
after repair.

### Static and workflow checks

All eight selected files passed `opengauss_screener.py --strict --json`,
`opengauss_cli.py refute --strict --json`, and
`opengauss_cli.py review --gate GATE_4 --json` after repair. Gate 4 is
explicitly a **static** result, distinct from the native kernel audit.
New-owner vacuity/placeholder scans are clean. The older
`JointCentralizerGeometry.dualSeed_trace_zero` regex signal was independently
classified as a false positive: its proof uses `h.pd.symm` and `h.dp`.
Workflow YAML, all five Bash blocks, and all three embedded Python blocks
passed syntax checks. The workflow includes all eight selected owners in
its hydration, compilation, zero-warning, and screening steps.

### Root-package boundary

The maintained `run_locked_lean.py` file check and
`run_locked_lake_build.py --wait-for-build-lock` with the eight explicit
targets were both attempted. They exit 1 **before elaboration** because the
root Lake package references missing
`external_refs/homotopy-hypothesis-lean4`. Exact-source closure acceptance is
therefore reported separately from root-package integration. The existing
draft publication scope and inherited gate disclosures in PR #304 apply.

The installed pre-commit hook passed for mathematical commit
`6d61838b31b5972eb00f0772a1da45eae54fe089`. The native `.githooks/pre-push`
hook was then executed for the exact update from published parent
`5a19e9da359692a14f6682b8588b3a0e591c9747` to that commit. It exited **1**:

1. The locked incremental Lake build stopped on the missing
   `HomotopyHypothesis` package before elaboration.
2. The semantic corpus audit selected **26,992** `lean/` files and reported
   two existing findings in `Physics/NuclearColimit.lean`: the definition
   `colimit_pairing_compat := True` and theorem
   `colimit_pairing_compat_trivial` proved by `trivial`. The scanner's lexical
   line/declaration labels are approximate; these names were confirmed by
   reading the actual source.

That file is outside the 43-module closure and byte-identical to original
main base `732d97c30f292d61ea332ca9da4d1e1d8f69bd00`, the parent PR head,
and the current mathematical commit: SHA256
`294541eb235d232b4ea132190efdc1dbb2f9a6743bc75d7e8885c4edc41aaf73`.
The hook's debt audit covered three changed Lean files and found zero open
gaps; tracked-scope and quarantine audits passed. The hook log SHA256 is
`b1abb4566edc8b180a63c460547e7c7647b5337c71aae6c7c398a4f87fe05639`.
Its detailed semantic report and source-equality receipt are retained under
`scratch/dual-seed-tilt-publication/`.

The following documentation-only commit records those observed gate outcomes.
The selected-source acceptance and the inherited root gate failure remain
separate; publication continues within the already authorized draft scope.

### Exact new-source identity

| File | SHA256 |
| --- | --- |
| `Core/DualSeedTilt.lean` | `bbb06debce6404e65835d7d890693ef14148eb1a5bfd4adde5716c9eefa39aaf` |
| `Canonical/JointCentralizerTilt.lean` | `a52cb6526b80cb590740efb84549739a5b80af721ca344243299536873fda819` |
| `Canonical/JointCentralizerTiltAudit.lean` | `9c144a9c8a975ae44cb43209c3d9e9890e392b81bb4ae7ff33be0350d8bb1694` |

Local evidence is retained in `scratch/dual-seed-tilt-review/`,
`scratch/dual-seed-tilt-qa/`, and `scratch/dual-seed-tilt-qa-supplement/`.
The dedicated GitHub workflow repeats exact-source verification for the
published commit and uploads its source, logs, and audit report.
