# Chiral Green operator: scope and verification record

**Native verification passed for both changed owners, with zero target warnings.**
The final native run reused all 20 compiled closure modules after fingerprint
validation and performed a fresh axiom audit of 57 owned declarations.
Scoped source gates also passed. The normal root-package entry points and the
publication gate are reported separately below.

## Provenance and changes

The [theorem contract](CHIRAL_GREEN_THEOREM_CONTRACT_20261116.md) records the
scope and the [preserved intake](CHIRAL_MOBIUS_WITTEN_INTAKE_20261116.md).
The source baseline is `08c34e03f610b452e03422037949196dc7d92d6d` of
`nickgou-nuke/info-geometry-lean`; the intake byte SHA-256 is
`0c090eb9ef05b43c17a291fb8fbdd6447afd26d669203f1c3a75f85fc05dd4cd`.

| Owner | Public additions | Total public declarations | Native audited declarations |
| --- | ---: | ---: | ---: |
| [`Analysis/HilbertGramDuality.lean`](../lean/InfoGeometry/Analysis/HilbertGramDuality.lean) | 3 | 14 | 31 |
| [`Singular/MoorePenroseChiralGreen.lean`](../lean/InfoGeometry/Singular/MoorePenroseChiralGreen.lean) | 24 | 24 | 26 |
| **Total** | **27** | **38** | **57** |

The additions comprise one definition and 26 theorems. The Green owner has
seven general star-ring theorems and 17 canonical Hilbert-space theorems.
The native count also includes generated auxiliary declarations; it is not
interchangeable with the count of named public source declarations.

## Proved mathematical scope

The carriers are complete real or complex Hilbert spaces, uniformly expressed
by `[RCLike 𝕜]`, without a finite-dimensional ambient-space assumption.
For a bounded `A : E →L[𝕜] F` and real `r > 0`, the native
`gramEigenspaceIsometryEquiv` acts on Mathlib's actual eigenspace submodules:

$$
U_r:E_r(A^\dagger A)\simeq_{\mathrm{isom}}E_r(AA^\dagger),\qquad
U_rx=(\sqrt r)^{-1}Ax,\qquad U_r^{-1}y=(\sqrt r)^{-1}A^\dagger y.
$$

For bounded self-adjoint `Q : E →L[𝕜] E` with closed range, set
`B := moorePenroseInverse Q hClosed`, using the existing constructed inverse.
The Green owner proves

$$
B^\dagger=B,\quad QB=BQ=P_{(\ker Q)^\perp},\quad
P_{\ker Q}=1-QB,\quad BP_{\ker Q}=P_{\ker Q}B=0,
$$

$$
\operatorname{range}(Q^2)=\operatorname{range}(Q),\qquad
(Q^2)^+=B^2,\qquad (Q^2)^+Q=B=Q(Q^2)^+.
$$

Closed range of `Q²` is derived before its canonical inverse is formed.
For **every bounded** `Γ` with `Γ * Q = -(Q * Γ)`, it also proves

$$
\Gamma B=-B\Gamma,\qquad
[\Gamma,P_{(\ker Q)^\perp}]=[\Gamma,P_{\ker Q}]=0.
$$

Here `Γ` need not be self-adjoint, invertible, or involutive. This strengthening
uses the group-inverse identities derived in the self-adjoint closed-range
setting; it does not assert general Moore–Penrose similarity covariance.

## Proof dependencies

1. The existing closed-range construction supplies all four Penrose laws.
   Existing star transport and uniqueness give self-adjointness of `B`.
2. Self-adjoint support gives `QB = BQ`; the commuting Penrose pair gives
   group-inverse identities, range equality, and the squared Penrose witness.
   Uniqueness then identifies the canonical inverse of `Q²`.
3. Native kernel/range orthogonality, closed range, and the existing range
   projection theorem identify the regular/kernel projections and annihilation.
4. A noncommutative ring argument transfers anticommutation to the inverse
   and gives support commutation. No global commutativity is assumed.
5. Independently, the existing Gram eigenspace equivalence and norm-squared
   law give the isometry after positive square-root normalization.

## Intake corrections and boundaries

Opposite Lie grades do not automatically give associative square-zero
operators. Reflexive inverse laws alone omit the two self-adjoint support
conditions required for Moore–Penrose inversion. For a square-zero reflexive
pair, both products of its two support projections vanish, so those supports
commute. A Weyl exchange relation alone does not uniquely force `S² = -1`.

Zero Witten index does not imply absence of zero modes or supersymmetry
breaking: equal nonzero chiral kernel dimensions give zero index. General
self-adjoint kernel/range decomposition requires the closure of the range;
closed range is explicit here. The Green formula uses Moore–Penrose inverses.

No spectral basis, compactness, global polar decomposition, unbounded Dirac
domain, heat trace, Fredholm index theorem, APS/Callias boundary problem, eta
invariant, continuum decomposition, metaplectic cover, or categorical colimit
is constructed. No physical vacuum-volume law or Landauer derivation follows.
The contract records primary references governing these interpretation limits.

## Native verification and inherited warnings

Evidence inspected: `chiral-development/report.json`, its `axioms.log`, and
`chiral-qa-native-check.json`. The native process exited 0; the report records
`status: passed` and `audit_required: true`. All 20 closure modules were compiled
successfully across the development runs. The final native acceptance run
fingerprint-reused **all 20**, then executed a **fresh native axiom audit**.
This was not a fresh recompilation of the entire closure in one final run.

The audit covers all 57 declarations owned by the two selected modules and
their transitive axiom dependencies. Its union is exactly `propext`,
`Classical.choice`, and `Quot.sound`. It is not an exhaustive declaration audit
of every imported module. Native QA confirms the source and staged hashes
match, and explicitly passes the two-target zero-warning gate.

| Frozen owner | SHA-256 |
| --- | --- |
| `Analysis/HilbertGramDuality.lean` | `83b17e3e7bdf858af910689c3937da69906433fde05943a6b8c8a52df43890c2` |
| `Singular/MoorePenroseChiralGreen.lean` | `72324457d199864bc5ee9ae67707c5524155f469adfde5bacae018ba5fa27448` |

The **25 inherited warnings** remain in five unchanged imported owners:
`Singular/MoorePenrose` (14), `Core/PeirceDecomposition` (1),
`Core/JordanPeirceDecomposition` (2), `Core/JordanAssociator` (7), and
`Singular/SquareZeroChiralHodge` (1). The two changed targets each have zero.
The checker has a prefix-specific automatic warning rule, so native QA
separately checked the selected targets. These results are scoped to this
closure and these owners; they do not certify the whole repository.

## Reproduction with pinned dependencies

Use Lean `leanprover/lean4:v4.34.1`, runtime commit
`5045d0056413266e57c625dcd7c365b10e377c52` (observed Linux x86-64 Release),
and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` with its initialized
matching dependencies. From the repository root, supply absolute paths:

```bash
CHIRAL_MATHLIB_ROOT=/absolute/path/to/mathlib-4.34.1
CHIRAL_LEAN=/absolute/path/to/lean-4.34.1/bin/lean
CHIRAL_QA_OUTPUT=/absolute/path/to/fresh-chiral-green-qa
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root "$CHIRAL_MATHLIB_ROOT" \
  --lean "$CHIRAL_LEAN" \
  --output "$CHIRAL_QA_OUTPUT" \
  --target InfoGeometry.Analysis.HilbertGramDuality \
  --target InfoGeometry.Singular.MoorePenroseChiralGreen
```

The checker acquires the shared build lock and verifies dependency/source
stability. This reproduction omits `--incremental` for a fresh rebuild;
the recorded acceptance used validated reuse as stated above. Keep the
native audit enabled. Inspect `report.json`, module logs, `axioms.log`, and
`evidence-sha256.json`, and require zero warnings in both target rows.

## Scoped source and semantic reviews

Independent owner/type review accepted both exact source hashes above.
The source gates ran serially on precisely the two changed owners:

| Check | Observed result |
| --- | --- |
| `semantic_content_audit.py --file-prefix <each owner> --gate` | Exit 0; both files read, complete selected coverage, zero findings. |
| `proof_proxy_staged_gate.py <both owners>` | Exit 0; PASS. |
| `placeholder_audit.py --root <owner> --strict` | Both exit 0; zero hard findings, three soft findings across both files. |
| `semantic_vacuity_gate.py <both owners> --fail-on error` | Exit 0; zero errors, three warnings. |
| `opengauss_cli.py refute <both owners> --strict --json` | Exit 0; zero detected traps. |
| `opengauss_cli.py review <both owners> --gate GATE_4 --json` | Exit 0; source review passes, with `kernel_unverified` as expected for this source-only command. |
| Scoped forbidden-token/debt scan | No matches for proof holes, custom axioms, unsafe proof shortcuts, or placeholder markers. |

The three placeholder soft findings concern one pre-existing definitional
readout and the explicit self-adjoint/closed-range and anticommutation
hypotheses. Those hypotheses are the mathematical contract, not assumed
inverse identities. The three vacuity warnings flag `rfl` evaluation lemmas:
two pre-existing Gram API readouts and the new normalized forward-map readout.
Each evaluates an already constructed equivalence; none replaces its
construction or norm proof. Source heuristics are not kernel evidence; the
native compilation and fresh axiom audit above provide that evidence.

## Root integration and publication boundary

An attempted locked file probe for `HilbertGramDuality.lean` has an
**indeterminate, interrupted outcome**. Its retained log contains only the
planned command, printed before lock acquisition. On resumption, the execution
service returned `Unknown process id 99298`; no process exit, owner elaboration,
or package error was observed. The queued successor probes produced no
recorded result. This attempt is not evidence of either root-build success or
a mathematical compilation failure.

The focused native proof result above therefore remains separate from root
package acceptance. Exact commands, observed exits, and integration logs are
kept in the delivery record.

The unchanged pre-push hook is an additional check against the resulting
commit. Its exact-commit result belongs in the PR or delivery record; this
source verification note does not certify publication or the whole repository.
