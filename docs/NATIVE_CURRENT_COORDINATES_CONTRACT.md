# Native Clifford current from eight real spinor coefficients

## Intent, provenance, and acceptance boundary

This task implements the concrete next obligation at the end of the supplied
report: encode the existing eight-field `STASpinor` record in the native even
Clifford algebra and identify the actual current's time component with the
already owned sum of eight squares.

The intake is preserved byte-for-byte in
[`NATIVE_CURRENT_COORDINATES_INTAKE_20261117.md`](NATIVE_CURRENT_COORDINATES_INTAKE_20261117.md).
Its SHA256 is
`7f06f6f9989819120a584963721f65f7eaa0e5c1aef0083360c54867f699d4a5`.
It reports earlier PR work; its verification claims are historical context,
not acceptance evidence for this source tree.

- Repository base: `08c34e03f610b452e03422037949196dc7d92d6d`.
- Branch: `codex/native-clifford-current-coordinates-20261117`.
- Finite algebraic scope: native real Clifford algebra of signature `(+---)`.
- Risk class: R4, because the source connects a physics-labelled coordinate
  record with an actual noncommutative algebra.
- Current disposition: `[qa_blocked]`; independent source review passed, while
  native compilation and recursive declaration axiom inspection are pending.
- Draft publication is for source review. It does not promote the candidates
  to `[kernel_verified]` or certify the whole repository.

The only prerequisite copied from another PR is
[`HestenesNativeDiracCurrent.lean`](../lean/InfoGeometry/Canonical/HestenesNativeDiracCurrent.lean),
from [PR #391](https://github.com/nickgou-nuke/info-geometry-lean/pull/391) at
head `9072e4c10f742659e624f4b8e357e13786744881`.
Its Git blob is `aade9c49f57608fa7f6acd3e9d257c40dacc0f85`; its SHA256 is
`8b744ca3d848fa3bb86f4760b2d3394d2bc7cc6397ccd6a800aabe4447f4b765`.
That file is carried unchanged and checked again in this PR's selected closure.
The broader PR #391 closure and PR #375 Fourier/QGT changes are not imported.

## Claim ledger

| Intake atom | Owner or construction | Scope and disposition |
|---|---|---|
| Eight real spinor coefficients and their density | Existing `SpacetimeAlgebra.STASpinor` and `STASpinor.current_j0` | Existing source-owned polynomial; prior owner status is not a fresh compiler result. |
| Encode the coefficients as an actual even multivector | New `HestenesNativeSpinorFrame.synthesis` and `HestenesSpinorCurrentBridge.encode` | Explicit construction; complete candidate proofs, native acceptance pending. |
| The sandwich is a spacetime vector | `synthesis_sandwich_eq_iota` and `diracCurrent_encode_eq_iota` | Equality of the full native Clifford elements, including spatial components. |
| The native time component is the eight-square density | Reused `hTrace_cl`, new `timeCoefficient_iota`, and `timeCoefficient_diracCurrent_encode` | Calibrated scalar readout is constructed from the existing native carrier. |
| Positive density detects a nonzero encoded spinor | Zero-set theorems, `synthesis_injective`, and `encode_injective` | Derived from the actual sandwich identity, without invertibility or normalization assumptions. |
| Encoded currents have nonnegative Minkowski norm | `currentVector_quadratic` and `currentVector_quadratic_nonneg` | Explicit finite polynomial consequence of the full native identity. |
| Positive density forces a strictly timelike current | Not claimed | False in the singular examples already present in the prerequisite. |
| Every native even element is encoded | No surjectivity or basis-completeness theorem added | `[bucket_3_open_debt]` for this bridge. |
| Observer covariance or a conserved field current | Requires additional group-action or PDE hypotheses | `[bucket_3_open_debt]`; not supplied by a pointwise algebraic identity. |
| Thermodynamic, vacuum-volume, or spectral interpretations | No new carrier or connecting theorem here | Outside this finite bridge. |

## Ground-truth owner search

Source search covered the active `lean/` owners, mirrored `src/` formulations,
imports, and consumers in the existing checkout before the isolated checkout
was created. Exact pinned Mathlib APIs were then inspected. This is a bounded
source search, not a graph-index completeness certificate.

| Existing owner | Reused content and observed boundary |
|---|---|
| `Canonical/HestenesSTA4DMaxwellDiracBridge.lean` | The eight-field record, `current_j0`, nonnegativity, and the literal zero-tuple characterization. It supplies no native Clifford encoder. |
| `Canonical/HestenesClPlus14.lean` | `V14`, `Q14`, `Cl14`, `ClPlus14`, `ι14`, `gamma`, their squares and anticommutation laws. |
| `Riemannian/CartanMetric.lean` | `hTrace_cl`, defined by exterior augmentation after the Clifford/exterior linear equivalence. No duplicate scalar-part definition is introduced. |
| PR #391 `Canonical/HestenesNativeDiracCurrent.lean` | Actual ordered sandwich `diracCurrent`, injectivity of `ι14`, and explicit singular null-current examples. |
| `Canonical/HestenesEvenPauliEquiv.lean` | A larger native even-algebra equivalence was inspected. It is not needed for this forward map; its selected import closure currently reaches the unresolved `proofs.CPTAtom` path. |
| `Canonical/HestenesPauliEvenClifford.lean` | A separate carrier using a nested-product vector space and `minkiQ`. Its frame cannot silently substitute for the `Fin 4 → ℝ` / `Q14` carrier. |

The three new owners import no Pauli equivalence and construct no complex
matrix surrogate. Existing low-level imported owners may also contain complex
definitions; that does not change the real types of the new maps and claims.

## Exact constructions and conventions

Use the existing real vector space `V14 = Fin 4 → ℝ` and quadratic form

\[
Q_{14}(v)=v_0^2-v_1^2-v_2^2-v_3^2.
\]

`Cl14` is Mathlib's `CliffordAlgebra Q14`; `ClPlus14` is its native even
subalgebra. The generator is `gamma i = ι14 (basisVec i)`. Reversion is
Mathlib's order-reversing `CliffordAlgebra.reverse`.

The real linear synthesis uses the ordered frame

\[
(1,\gamma_0\gamma_1,\gamma_0\gamma_2,\gamma_0\gamma_3,
\gamma_2\gamma_3,\gamma_3\gamma_1,\gamma_1\gamma_2,
\gamma_0\gamma_1\gamma_2\gamma_3).
\]

The order `gamma 3 * gamma 1` is retained. The boost blades are the negatives
of the existing `sigmaEven` generators, which use `gamma i * gamma 0`.
Products are the actual noncommutative Clifford products throughout.

For coefficients `c : Fin 8 → ℝ`, the full current candidate theorem is

\[
\operatorname{synthesis}(c)\,\gamma_0\,
\widetilde{\operatorname{synthesis}(c)}=\iota_{14}(J(c)),
\]

with

\[
\begin{aligned}
J_0&=\sum_{i=0}^7c_i^2,\\
J_1&=2(-c_0c_1+c_2c_6-c_3c_5-c_4c_7),\\
J_2&=2(-c_0c_2-c_1c_6+c_3c_4-c_5c_7),\\
J_3&=2(-c_0c_3+c_1c_5-c_2c_4-c_6c_7).
\end{aligned}
\]

The proof expands native products and reversion, then uses generator squares
and ordered anticommutation to normalize Clifford words. Mathlib's `module`
tactic collects real coefficients after that reduction. It does not commute
the Clifford generators or replace them by scalar coordinates.

The scalar readout is the already owned `hTrace_cl Q14`. The new lemmas derive

\[
\operatorname{hTrace}_{cl}(\iota_{14}(v)\iota_{14}(w))
=v_0w_0-v_1w_1-v_2w_2-v_3w_3
\]

from Mathlib's `changeForm_ι_mul_ι` and polarization. In particular,
`equivExterior` is used as a linear equivalence, never as an algebra
homomorphism. Define the real linear functional

\[
\operatorname{timeCoefficient}(X)
=\operatorname{hTrace}_{cl}(X\gamma_0).
\]

Its calibration on every included vector is proved as
`timeCoefficient (ι14 v) = v 0`.

The record equivalence orders the fields as
`s0, b01, b02, b03, b23, b31, b12, p`. Composing it with synthesis gives
`encode`. The main compatibility statement is exactly

```lean
theorem timeCoefficient_diracCurrent_encode (ψ : STASpinor) :
    timeCoefficient (diracCurrent (encode ψ)) = STASpinor.current_j0 ψ
```

No result is assumed in a structure field. Applying the zero-density
characterization to `synthesis (c - d)` proves synthesis injectivity. The
record encoder is injective by composition. Zero full current, zero native
encoded element, and the zero record are related by explicit equivalences.
The current is in `LinearMap.range ι14`, and the representing vector is unique
by the prerequisite's injectivity theorem.

The exact norm formula is

\[
Q_{14}(J(c))=
(c_0^2-c_1^2-c_2^2-c_3^2+c_4^2+c_5^2+c_6^2-c_7^2)^2
+4(c_0c_7-c_1c_4-c_2c_5-c_3c_6)^2.
\]

Together with positive `J₀` for nonzero coefficients, this describes a future
causal current in the selected frame. The formula permits a nonzero null
current. It does not assert strict timelikeness, a complete Fierz package, or
a dynamical conservation law.

## Dependency order

The logical order is native generator relations and reversion → full
sandwich/vector equality; native scalar contraction and polarization →
calibrated time readout; those two results plus the coefficient equivalence →
the existing density compatibility; definite density and linear subtraction →
injective synthesis and exact zero sets. The norm formula is a separate
polynomial consequence for the identified vector. No analogy serves as a
dependency edge.

## Independent review

Generation and source review were separate assignments. Two independent
reviewers checked the readout and frame, and two reviewers checked the
integration. They found no mathematical correction or obvious pinned-API
mismatch in the following exact candidate sources:

| Owner | SHA256 reviewed |
|---|---|
| `HestenesCurrentReadout.lean` | `12ad941019c783b0786ff6939fbe5fc7fdb4171979d68318a081b7965da5dd71` |
| `HestenesNativeSpinorFrame.lean` | `9956611de916cca4071b68e5c84c24da3b1ea1a9e11dda20b3e832a0fc822c75` |
| `HestenesSpinorCurrentBridge.lean` | `ea8d1d61646b96c8aa6e3f454207cbe4c6e5a4755c0c577b9b9c83c8a8aaca64` |

The reviews checked the contraction sign, polarization factor, right
multiplication convention, spatial current signs, coefficient inverse,
finite-sum API, strict-positivity direction, range witnesses, and the
noncircular injectivity argument. No reviewer ran a compiler. These findings
are source-review evidence only.

## Verification plan and observed state

The unchanged environment pins are Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
The maintained selected-closure checker resolves **8 repository modules** and
**15 distinct direct Mathlib import roots**. Those are import-root counts,
not the size of Mathlib's transitive dependency graph.

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/44e3088154ac/mathlib4 \
  --lean /workspace/scratch/50ddde16aff2/runtime/lean-4.34.1-linux/bin/lean \
  --output /workspace/scratch/d8c17edeea4e/native-current-verification \
  --target InfoGeometry.Canonical.HestenesNativeDiracCurrent \
  --target InfoGeometry.Canonical.HestenesCurrentReadout \
  --target InfoGeometry.Canonical.HestenesNativeSpinorFrame \
  --target InfoGeometry.Canonical.HestenesSpinorCurrentBridge
```

The local run has reached `Waiting for shared build lock`. No completed
module or axiom result has been observed. This is a pending validation attempt,
not a successful check or a reported mathematical failure.

The focused workflow uses the same maintained checker without `--skip-audit`,
requires all four target modules to have zero warnings, runs strict placeholder
and semantic-error checks, and uploads source hashes, compiler logs, the native
axiom report, and generated audit source even when a check fails. The permitted
axioms are `propext`, `Classical.choice`, and `Quot.sound`; the actual footprint
must come from that native report.

The pre-existing `.github/workflows/post-build-gate.yml` ended with a stray
`EOF` token. This PR removes only that token so GitHub can parse the existing
quality workflow. No gate step or acceptance criterion is weakened.

This task uses an independent Git checkout, not a linked worktree, with tracked
hooks installed. A sparse checkout conserves the remaining local disk space;
every source in the selected closure is materialized. Whole-root local
acceptance cannot be inferred from this sparse selected surface. The focused
CI job fetches the full exact Git source tree. Root-package and historical
dependency blockers remain separate from this eight-owner closure.

Outstanding acceptance work is the completed native check and recursive axiom
audit, zero-warning confirmation, and the actual tracked pre-push result.
The PR remains draft until its required evidence is available.

### Completed selected source checks

The parent ran the following source checks on all four target files, separately
from the queued compiler attempt:

```bash
python3 tools/quality/placeholder_audit.py --root <target-file> --strict
python3 tools/quality/semantic_vacuity_gate.py <four-target-files> --fail-on error
git diff --check
```

All commands returned zero. The strict placeholder checks reported **zero hard
findings and six soft findings**. The semantic error gate reported **zero
errors and nine `trivial_surface` warnings**. These are not zero-finding results
and are not compiler-warning counts.

The reviewed findings concern transparent definition/application lemmas,
included-generator reversion, literal zero cases, and finite real-polynomial
proofs. Their conclusions match the definitions or reduce to the displayed
polynomial identities. They do not replace the substantive sandwich, scalar
contraction, or injectivity theorems. The complete native axiom audit remains
necessary to verify the proof terms.

Both workflow documents parsed as YAML; the existing workflow retains all its
steps after the single stray-token removal. The preserved intake matched the
attachment byte-for-byte. These observations establish source provenance and
syntax at the stated scope only.
