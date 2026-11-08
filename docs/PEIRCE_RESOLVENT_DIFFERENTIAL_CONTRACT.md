# Peirce conjugation and the noncommutative resolvent differential

## Intake and provenance

This continuation formalizes the algebraic and differential content of the
user's attachment `Pasted text(7).txt`, received on 2026-11-06. The original
attachment has 27,760 bytes and SHA-256
`7ab8a4b7a2006afa04549753c7289bd7ec539953d0d7f8308d21b9cbab9b52bc`.
Its opening is “Phase I: The Fundamental Binary Cut (Thesis vs. Shadow)”;
its subject is the proposed Super-Grassmannian / Para-Kähler continuation.
The original attachment is retained separately from the mathematical owners.

The intake proposes Peirce tangent polarization, two single-corner idempotent
charts, a two-corner conjugated idempotent, resolvent intertwining, a factored
differential, and identifications with Berezinian, Amari, and split-octonion
geometry. It contains two different conjugation conventions. The final
“Canonical Axiomatic System” corrects the earlier expansion. This contract
uses that final convention and records the distinction explicitly.

Base checkout: `3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`, fetched from upstream
`main`. This is a separate continuation from the polynomial/colimit work in
PR #289; it does not depend on that PR. Toolchain and dependency pins are
unchanged.

## Carriers and ordered primitives

For the algebraic results, `B` is an arbitrary associative unital ring. It is
not assumed commutative, a division ring, finite dimensional, or equipped with
an order. Let `P * P = P`, put `Q = 1 - P`, and reuse the existing definitions
in `InfoGeometry.OperatorAlgebra.PeirceSpine`:

```text
a = conePlus P A  = P * A * Q
c = coneMinus P C = Q * C * P
Phi   = genPhi P A C = a + c
V     = genV P A C   = a*c + c*a
Sigma = genSig P A C = a*c - c*a.
```

The complementary corners satisfy `P*a=a`, `a*P=0`, `P*c=0`, `c*P=c`.
Products of any two upper corners vanish, as do products of any two lower
corners. Mixed products retain their multiplication order. The names `V` and
`Sigma` in these owners denote ring expressions; a scalar metric or curvature
tensor is additional mathematical data.

The inverse throughout this addition is Mathlib's `Ring.inverse`. In a general
ring this function is zero on nonunits. Every inverse cancellation and every
analytic derivative below therefore carries the relevant `IsUnit` hypothesis.
Writing an inverse symbol is not an invertibility proof.

## Existing owners and the missing implications

The bounded source search covered the relevant PeirceSpine, Algebra, Core,
Canonical, Analysis, SuperGrassmannian, and NCG owners, their declarations and
consumers, and the pinned Mathlib inverse and Fréchet-calculus APIs.

| Existing owner | Actual content used or distinguished |
|---|---|
| `OperatorAlgebra/PeirceSpine/Basic.lean` | Ordered corners and their annihilation laws over `[Ring B]`; the `peirce_nf` normalizer retains the order of products |
| `Core/IdempotentTangent.lean` | `P*H+H*P=H` iff the diagonal corners of `H` vanish; reconstruction from the two off-diagonal corners; double-commutator involution |
| `Core/PeirceMatrixPerfectPairing.lean` | Actual upper/lower corner range submodules over a field and their perfect trace pairing; no supermanifold structure is inferred from this linear duality |
| `Core/IdempotentGraphGrassmannian.lean` | The set of ring idempotents and exact idempotency-defect identities; this set alone is not a supermanifold construction |
| `OperatorAlgebra/PeirceSpine/Unipotent.lean` | Inverse unipotent conjugations, their group-action and polynomial laws; its named single charts use different signs/base projectors from this intake |
| `OperatorAlgebra/PeirceSpine/Bergman.lean` | The ordered polynomial Bergman operator, its transport identities, and Jordan-triple identities; no analytic inverse is supplied by these polynomial identities |
| `Canonical/OperatorResolventSpine.lean` | A units-based resolvent-difference identity and finite geometric sums, including a Fock-operator specialization |
| `Canonical/OperatorLogDetDikinGeometry.lean` | Actual ordinary-trace log-determinant Hessian on full finite complex matrices; positivity and barrier estimates require a strictly positive base and self-adjoint directions |
| `OperatorAlgebra/PeirceSpine/GradedTraceMoments.lean` | Cyclic Peirce-supertrace cancellation for positive powers of `V`; it does not supply an independent Bose–Fermi grading |
| `NCG/BerezinianExponentialSupertrace.lean` | A real block-diagonal exponential/determinant-ratio identity with ordinary block traces; the blocks and operation are explicitly defined |
| `Canonical/OperatorBerezinianDifferential.lean` | An ordered ratio of arbitrary units and its right logarithmic derivative; this does not identify a generic ring expression with a scalar Berezinian |
| Mathlib `Algebra.Algebra.Spectrum.Basic` | The nonzero-spectrum product-swap theorem, yielding the Jacobson unit equivalence for `1-A*C` and `1-C*A` |
| Mathlib `Analysis.Calculus.FDeriv.Mul` | The genuine derivative of `Ring.inverse` at units and product rules for noncommutative normed algebras |

The additions connect these ingredients through the corrected conjugation
convention, a reusable resolvent transform, its exact finite difference and
remainder, and its actual Fréchet derivative. They do not introduce a new
tangent carrier, determinant, trace, or abstract geometry with its desired
properties supplied as fields.

## Precise theorem contracts

### 1. Corrected two-corner conjugation

The chosen ordered expression is

```text
(1-a) * (P+c) * (1+a) = P + Phi - Sigma - V*a.
```

It is idempotent because `P+c` is idempotent and `1-a`, `1+a` are two-sided
inverses. Both the quadratic correction `-Sigma` and the cubic correction
`-V*a` are present. The opposite conjugation has the different expansion

```text
(1+a) * (P+c) * (1-a) = P - a + c + Sigma - V*a.
```

Neither formula permits replacing `a*c` by `c*a`.

The difference is substantive. In `Mat₂(ℤ)`, take `P=e₁₁`, `a=e₁₂`, and
`c=e₂₁`. Direct matrix multiplication gives the earlier claimed expression
`[[2,0],[1,0]]`, whose square is `[[4,0],[2,0]]`; the corrected expression is
the idempotent `[[0,0],[1,1]]`. In this same example `V=1`, so `1-V=0` is
not a unit. Thus unconditional dressed idempotency does not supply the
invertibility hypothesis for the subsequent resolvent results.

### 2. The resolvent transform on the unit locus

For arbitrary `A,C : B`, without Peirce assumptions, define

```text
eta C A = Ring.inverse (1-A*C) * A.
```

Prove the native Jacobson equivalence

```text
IsUnit (1-A*C) ↔ IsUnit (1-C*A).
```

Under this equivalent unit hypothesis, prove

```text
inverse(1-A*C) * A = A * inverse(1-C*A)
inverse(1-C*A) = 1 + C * inverse(1-A*C) * A.
```

For a second input `D` on the same unit locus, the exact finite difference is

```text
eta C D - eta C A
  = inverse(1-D*C) * (D-A) * inverse(1-C*A).
```

Consequently, if both `A` and `A+H` are on the unit locus, the remainder after
subtracting the factored linear expression is exactly

```text
eta C (A+H) - eta C A
  - inverse(1-A*C) * H * inverse(1-C*A)
  = inverse(1-(A+H)*C) * H * C * inverse(1-A*C)
      * H * inverse(1-C*A).
```

This is a ring identity, including the displayed multiplication order. It is
not an assertion that a general second-order remainder vanishes.

### 3. Peirce specialization

For `qPlus=a*c`, `qMinus=c*a`, the corner laws prove

```text
(1-qPlus) * (1-qMinus) = 1-V
  = (1-qMinus) * (1-qPlus).
```

On the resulting equivalent unit loci, the inverse of `1-V` acts on an upper
corner on the left like the inverse of `1-qPlus`, and on the right like the
inverse of `1-qMinus`. These statements apply to an arbitrary upper variation
`H=P*X*(1-P)`, not just the base coordinate `a`:

```text
inverse(1-V) * H * inverse(1-V)
  = inverse(1-qPlus) * H * inverse(1-qMinus).
```

The proof uses the annihilations `qMinus*H=0` and `H*qPlus=0`. It does not
assume `H` commutes with `V`. Multiplication by any lower variation preserves
this equality, but produces an operator-valued expression rather than a
scalar metric.

### 4. Actual Fréchet derivative

For the analytic theorem, strengthen the carrier to a complete real normed
algebra: `[NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]`. The carrier
remains noncommutative; full matrix Banach algebras are included.

If `IsUnit (1-A*C)`, prove native `HasFDerivAt` for the function `eta C` at
`A`, with the continuous linear map

```text
ContinuousLinearMap.mulLeftRight ℝ B
  (Ring.inverse (1-A*C)) (Ring.inverse (1-C*A)).
```

Applied to `H`, this derivative is exactly
`inverse(1-A*C) * H * inverse(1-C*A)`. The coordinate `C` is fixed. This is
a theorem in Mathlib's analytic derivative semantics, not a definition that
names the desired expression “the derivative”. A bare ring has no topology
with which to state that analytic claim.

The Peirce specialization composes this actual derivative with the native
continuous linear projection `X ↦ P*X*(1-P)`. For the raw upper coordinate
map `X ↦ eta (coneMinus P C) (conePlus P X)`, the derivative at `A` is the
native `mulLeftRight` map with left factor `inverse(1-V)*P` and right factor
`(1-P)*inverse(1-V)`. This also specifies precisely how the uncompressed
coordinate and the actual upper variation are related.

## Dependency order

| Layer | Established input | Resulting obligation |
|---|---|---|
| Corner algebra | Idempotence of `P`, existing Peirce laws | Ordered conjugation expansion and idempotence |
| Unit algebra | Associativity and native units/inverse | Product-swap unit equivalence and push–pull |
| Exact response | Unit algebra at both endpoints | Finite difference and explicit quadratic remainder |
| Corner response | Unit algebra plus same-corner annihilation | Full-resolvent / corner-resolvent factorization |
| Analytic response | Real Banach-algebra structure and inverse calculus | Genuine `HasFDerivAt` with the factored derivative |

These are mathematical dependencies. The interpretive identifications below
are not edges in this proof chain.

## New owner interfaces

Paths are relative to `lean/InfoGeometry/`. There are 25 explicit theorem
declarations and the single definition `ResolventTransform.eta`.

| Owner | Main exported declarations |
|---|---|
| `OperatorAlgebra/ResolventTransform.lean` | `isUnit_one_sub_mul_iff`, `push_pull`, `inverse_one_sub_mul_reverse`, `eta_sub`, `eta_add_sub_sub_linear` |
| `OperatorAlgebra/PeirceSpine/Resolvent.lean` | `same_base_chart_commutator_eq_zero_iff`, `conjPlusInv_lower_chart_eq`, `conjPlusInv_lower_chart_idempotent`, `isUnit_one_sub_genV_iff`, upper/lower `inverse_one_sub_genV_conePlus_sandwich` / `inverse_one_sub_genV_coneMinus_sandwich` |
| `Analysis/ResolventTransformDifferential.lean` | `hasFDerivAt_eta`, `fderiv_eta_apply` |
| `Analysis/PeirceResolventDifferential.lean` | `hasFDerivAt_eta_conePlus`, `fderiv_eta_conePlus_apply` |

## Corrections and unproved interpretations

| Intake claim | Status and precise boundary |
|---|---|
| The early dressed expansion is `P+Phi+qPlus-V*a` | Incorrect; the final corrected convention includes `-Sigma` and reverses the conjugating signs |
| `V*a` is the existing Jordan triple product of `a,c,a` | With the repository convention `jordanTriple a c a = a*c*a+a*c*a`, the symmetrized triple is `2*(V*a)`. The cubic correction itself is the ordered word `a*c*a` |
| The two-chart commutator or naive idempotency defect is always nonzero | Overstrong; zero corners give zero. Nonvanishing needs a hypothesis or witness |
| The chiral involution acts by opposite signs on the two tangent corners | True for left multiplication by `2P-1`; conjugation by `2P-1` acts as minus the identity on both odd corners. These are different actions |
| The resolvent coordinate is a left/right module homomorphism | Unsupported and generally false as a function of its input: the inverse itself depends on `A`. The push–pull equation is an intertwining identity |
| Every displayed differential statement is a theorem over `[Ring B]` | Exact response identities are algebraic. A genuine Fréchet derivative additionally uses a norm, scalar action, and the analytic inverse theorem |
| The product of two varied operators is a metric | A pairing or trace, symmetry, nondegeneracy, and a domain must be supplied and proved |
| At the origin, `dNPlus*dNMinus = (V+Sigma)/2` for the base `V,Sigma` | Confuses variation data with base coordinates. At zero base the latter vanish, while the product of two variations need not vanish |
| The Peirce decomposition defines a para-Kähler supermanifold with flat Amari connections | The ring identities do not construct the manifold, graded coefficient algebra, nondegenerate two-form, integrability, or dual connections |
| All ring idempotents are interchangeable with ordinary Grassmannian subspaces | An idempotent records both image and complementary kernel; unipotent conjugation need not preserve self-adjointness |
| The proposed supertrace potential is automatically a Dikin barrier | The existing Dikin owner uses ordinary trace on a positive cone. A nonlinear pullback, different signature, or supertrace requires a separate theorem |
| The Bose–Fermi grading is interchangeable with the Peirce grading | An independent grading requires explicit data. For the Peirce grading, the existing positive-power supertrace cancellation makes every coefficient of the proposed formal logarithmic potential vanish |
| Two named gradings automatically define an action of the Klein four-group | The two involutions must also commute; this compatibility needs proof |
| `-STr log(1-V)` equals a logarithmic Berezinian | Requires a correctly typed Berezinian and a logarithm with appropriate domain or formal-series semantics; no such identity follows from a plain ring expression |
| Split octonions embed as an algebra into the associative ring used here | A multiplication-preserving injective map into an associative ring would force associativity. A linear operator representation or a selected associative subalgebra is a different construction |

No theorem in this addition asserts these missing geometric identifications.
There are no custom axioms, proof holes, scalar replacements for the operator
carrier, or assumed conclusion fields.

## Validation

Compiler: Lean `4.34.1`, commit
`5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

| Check | Result and scope |
|---|---|
| Independent mathematical source review | PASS for all four new owners and this theorem contract |
| Fresh selected source-closure compilation | PASS: 14 project modules, comprising four new owners and ten unchanged dependencies |
| Compiler warnings in the new owners | Zero |
| Independent rebuild and complete native declaration audit | PASS: four new owners recompiled independently; all 43 owned declarations, including generated proof helpers, audited |
| Staged proof-source gate | PASS |
| Root Lake integration | Not certified; the pinned `external_refs/gift-framework-core/lakefile.lean` is missing |

The successful source-closure command, from the repository root, was:

```bash
source /workspace/scratch/2e3cbf77ee2a/runtime/environment.sh
python3 tools/quality/check_operator_geometry.py \
  --repo /workspace/scratch/2771a9ff6f38/info-geometry-lean \
  --mathlib /workspace/scratch/2e3cbf77ee2a/runtime/mathlib \
  --work-dir /workspace/scratch/2771a9ff6f38/verification/resolvent/development-final \
  --target InfoGeometry.Analysis.PeirceResolventDifferential
```

The selected source-closure PASS receipt has SHA-256
`1c5e1db8ca4f312a5566c2f65e8da4c2c0f85e614ec99f47e98c9e7863eff72b`.
Every project module in that closure was compiled from its recorded snapshot;
no borrowed project artifacts were seeded into this development run. The
unchanged Mathlib cache was used at the repository pin.

The independent reviewer then recompiled all four new owners into a separate
artifact root. Only the ten unchanged dependency artifacts were reused, after
checking their source snapshots, Git blobs at base
`3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`, compiler logs, toolchain and
package pins, and artifact hashes. No new-owner artifact was copied into the
independent run.

The successful independent command, from the repository root, was:

```bash
source /workspace/scratch/2e3cbf77ee2a/runtime/environment.sh
python3 /workspace/scratch/2771a9ff6f38/verification/resolvent/qa/run_qa.py \
  --repo /workspace/scratch/2771a9ff6f38/info-geometry-lean \
  --reference /workspace/scratch/2771a9ff6f38/verification/resolvent/development-final \
  --mathlib /workspace/scratch/2e3cbf77ee2a/runtime/mathlib \
  --lean /workspace/scratch/2e3cbf77ee2a/runtime/lean-4.34.1-linux/bin/lean \
  --work /workspace/scratch/2771a9ff6f38/verification/resolvent/qa/final-2 \
  --development-log /workspace/scratch/2771a9ff6f38/verification/resolvent/development-final.log
```

The task-local runner, SHA-256
`6258bb382eddd7d10b4eabb3381d5e79afd27e33fcd4f7acd4da5587fe4e499b`,
used the repository's unchanged
`tools/quality/reviewed_audit_source.py` implementation for the native audit.

The native complete-declaration audit checked 12 declarations in
`ResolventTransform`, 26 in `PeirceSpine.Resolvent`, three in
`ResolventTransformDifferential`, and two in `PeirceResolventDifferential`.
The total of 43 includes generated proof helpers in addition to the 25
explicit theorems and one definition. The observed foundational axioms were
exactly `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom,
proof hole, unsafe declaration, or partial declaration was accepted. All
four independent compiler logs were empty, and the declaration audit exited
successfully without warnings.

The successful independent receipt,
`verification/resolvent/qa/final-2/qa-result.json` in the task workspace, has
SHA-256
`dbeabbc0ac920ecb044563730520c3895d940d8e1ae3596a0467e93f3e34afa1`.
The complete audit log has SHA-256
`35d2598f38b7d287ce612ded9783d76cd840c26f55b82275ce6800818b986476`.
The first independent attempt failed at the compiler launcher's version
query, before any new-owner compilation. Its failure receipt is retained
separately. The successful retry used the existing runtime environment and
executable-path compatibility shim also used by the development build; it
did not change the compiler, dependency pins, sources, or audit implementation.

The four new source hashes are:

| Source | SHA-256 |
|---|---|
| `OperatorAlgebra/ResolventTransform.lean` | `21ac28966bfa474d4a2d3cdfff8019ca5d970113367d5e814234c3a048c9524c` |
| `OperatorAlgebra/PeirceSpine/Resolvent.lean` | `bbeb7ae0cf29928889032aa0a4c9d5184f162adc2cad0beea63872885f4eee70` |
| `Analysis/ResolventTransformDifferential.lean` | `241c02bbfd64baa804f692f1019a1247f8c30fdfdc9d4b16328b19e31266b905` |
| `Analysis/PeirceResolventDifferential.lean` | `8246851caff00776e1f1246a65e7e1fd199e1c2221f0281a23518e8bc8d94615` |

This is selected-owner evidence, not a whole-repository build certificate.
The ordinary repository gate and its external dependency configuration remain
separate from these mathematical source checks.
