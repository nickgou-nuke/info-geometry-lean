# Native Zorn null kernels and real Clifford reciprocity

## Frozen intake and scope

Source: the attached `Pasted text(20261124-132851).txt`, 36,159 bytes,
SHA-256 `e9015139d818aa18e98c5b37aed417ca17632b24af056746ccce071fd4147ee8`.
The adjacent `zorn-null-born-20261124-intake.txt` preserves the exact bytes as
evidence. Source review began on PR #447 commit
`b8fc169c39833caf24040f5c3a2d222c6a8af46d`, above PR #441 commit
`30fb78352e609a860bd6d406f1352a4a863738e1`.

This R4 packet concerns finite real algebra on the existing canonical Zorn
carrier and its existing doubled sixteen-dimensional module. The intended
dependency order is contraction and trace, nonzero-null kernel dimension,
quadratic coordinate transport, normalized Witt operators, the four-negative
generator product, and the oriented Clifford volume action. Each displayed
identity remains a source candidate until its exact Lean snapshot and axiom
dependencies have been checked.

## Intake audit

The pasted multiplication table is inconsistent with its composition claim.
It gives `e4 * e4 = 1`, `e4 * e1 = e5`, and `e4 * e5 = -e1`, so
`L(e4)^2(e1) = -e1`. With the pasted conjugation and norm,
`L(e4) L(conj e4)(e1) = e1` whereas `N(e4) e1 = -e1`.
It also gives `e2 * e5 = e7 = e5 * e2` for distinct imaginary units.

For `x = 1 + e4`, that table gives `N(x) = 0` and a one-dimensional left
kernel. On each spatial two-plane `L(e4)` squares to `-I`, so `I + L(e4)`
is invertible there; only the scalar/pole plane contributes to the kernel.
The proposed seven-factor integer certificate sends `e2` to `-e2`.
Consequently neither the claimed four-dimensional kernel nor the proposed
`decide` certificate is accepted from the intake. The actual native product
is the owner of all promoted statements.

The normalized Witt formulas are sound for genuine signed Clifford
generators. Both the sum and difference require the factor `1/2` to obtain
mixed anticommutator `I`. The unscaled pair gives `4 I`. The attached final
theorem asserts matrix identities, while the existing
`Canonical.ZornCliffordFaithful` separately constructs the actual algebra
equivalence from the universal representation.

## Native owners and exact targets

| Target | Existing owner and intended implication |
| --- | --- |
| Actual real carrier and action | Reuse `Canonical.ZornMatrix`, `ZornClifford.zornNorm`, `zornConj`, `diracGammaLinear`, and `zornCliffordRepresentation`; reuse `SplitOctonionEllCircularPeirceBasis.leftRegularRepresentation`. |
| Conjugate contractions | Reuse `Lie.CanonicalZornRegularNorm.leftRegular_mul_conj` and `conj_mul_leftRegular`; derive their bilinear polarizations. |
| Operator trace | Prove `trace (L X * L (conj Y)) = 4 * P X Y` for the unhalved native form `P = zornNorm.polarBilin`. The intake's half-polar form is `B = P/2`, giving `8 * B X Y`. |
| General nonzero-null kernel | For `X ≠ 0` and `N X = 0`, prove `range (L (conj X)) = ker (L X)` and `finrank ℝ (ker (L X)) = 4`. Existing annihilator results require an imaginary element and right multiplication. |
| Projection dimension | Reuse Mathlib `IsIdempotentElem.isProj_range` and `LinearMap.IsProj.trace`, together with rank-nullity. |
| Norm coordinates | Reuse `SplitOctonionQuaternionZornCoordinates.cartesianZornLinearEquiv` and its determinant/norm identity, then construct the required Fin-8 coordinate isometry. |
| Normalized CAR | Transport existing `Clifford.Cl44Witt.a`, `adag`, and their CAR through the proved quadratic isometry and existing real Zorn action. |
| Born product | Use the ordered product of the four existing negative Clifford generators; prove its square, commutation/anticommutation, and conjugation exchanging the two normalized Witt families. |
| Ordered volume | Reuse `Clifford.Cl44VolumeElement.volumeElement`. Establish explicit oriented generator readouts before asserting that its native doubled action is `(s,t) ↦ (s,-t)`. |

## Conventions and boundaries

The native Zorn product uses minus the lower-vector cross product in its upper
slot and plus the upper-vector cross product in its lower slot. The existing
Cartesian norm map is
`((q0,q),(r0,r)) ↦ (q0+r0, q0-r0, q+r, r-q)`.
Relative to the prior packet's `q_i = lower_i - upper_i` and
`f_i = -(upper_i + lower_i)`, the ordered diagonal axes are
`(1,-q0,-q1,-q2,ell,-f0,-f1,-f2)`.
The six spatial sign reversals preserve orientation. This coordinate fact
does not substitute for the represented volume proof.

The nonzero hypothesis is essential: the zero operator has kernel dimension
eight and conjugate range zero. An arbitrary null element need not have
trace zero, so its left action need not square to zero. The correct general
range is the range of its conjugate action. Scalar octonion trace and
eight-dimensional operator trace are kept distinct.

No analytic, dynamical, physical, or group-classification result is inferred
from these finite identities. All operators retain their actual ordered
composition. The underlying Zorn product remains nonassociative.

## Roles and verification plan

`audit_math` audited the table and authors the isolated general null-kernel
owner. `source_scout` mapped existing owners and authors the isolated
quadratic/Witt/Born transport. Root integrates independently reviewed sources
and the oriented volume consumer. `final_qa` owns the serialized compiler and
gate lane using the maintained shared build lock.

The parent and base PRs have actual compiler diagnostics to repair first:
the native norm owner now builds; the full determinant expansion times out;
the Witt owner has tactic warnings; triality has a notation precheck and two
algebra-normalization failures; the faithful bridge has one duality-evaluation
mismatch. Those observations are tied to recorded current-head CI artifacts,
not inferred from static scans. Publication and verification updates will
record the exact repaired revisions, source hashes, compiler outcomes, and
axiom audit separately.

Initial new-packet status: source construction pending. No proof holes, custom
axioms, native evaluation bypasses, changed pins, weakened gates, or claims of
whole-repository acceptance are permitted.

## Reviewed implementation snapshot

The new branch is `codex/zorn-null-born-20261124`, based on the published
PR #447 repair `22b2ec6072f8872b5e5fd15df9de4d425afa35c8`. That commit
preserves both prior histories and includes parent PR #441 revision
`98d294795ee7356b2b98c827bc739bc04e01b298`.

| Owner | SHA-256 | Public heads | Independent source review |
| --- | --- | --- | --- |
| `Lie/CanonicalZornNullKernel.lean` | `51359a1044c6fb46cbbb998f851ef66f804f377f98fb95bc5c1d8e2431869113` | 7 theorems | `source_scout` reviewed `audit_math`'s source: PASS |
| `Canonical/ZornWittBorn.lean` | `a3463f09524582fd12576201e407792570fbf4cb1e8d60db73ab330edf098d9d` | 25 theorems, 5 definitions | `audit_math` reviewed `source_scout`'s source: PASS |
| `Canonical/ZornVolumeAction.lean` | `57b46259ea25d7bed3e43ca2acc1727fad4bd6284cfa8db34cfe6a18604115cb` | 4 theorems | `audit_math` reviewed root's source; two redundant terminal tactics removed, statements preserved: PASS |

The null-kernel owner computes only the eight diagonal entries needed for
the regular trace. Polarizing the native conjugate contractions and using
cyclic trace gives the factor-four identity. A polar partner with `P X Y = 1`
provides an explicit conjugate-range preimage of each kernel vector. The
operator `T = L X * L (conj Y)` is an actual idempotent with the same range
as `L X` and trace four. Mathlib's projection trace and rank-nullity give
kernel dimension four. Existing norm multiplicativity then proves that
every vector in this kernel has zero norm.

The Witt/Born owner constructs its finite-function coordinate equivalence
from native Mathlib equivalences, composes it with the existing quaternion
coordinate map, and proves the norm isometry. The universal Clifford
isometry is composed with the original real Zorn representation. Existing
normalized `a` and `adag` elements supply all indexed CAR and nilpotency
relations. The four-negative product has square one and its conjugation
exchanges these same two families.

For the volume sign, two sparse native left-action products both give
`R(a,b,x,y) = (b,a,-y,-x)`: the three positive imaginary directions and the
four negative directions. The positive four-gamma product is
`diag(R,-R)`, and the represented Born product is `diag(R,R)`. Their ordered
product is therefore `diag(I,-I)`. The final theorem anticommutes this exact
operator with every native vector gamma. No eight-fold matrix expansion or
unchecked integer certificate is used.

The checker selects the three new owners and the existing faithfulness and
full-Cl(4,3) noninjectivity owners. The source inventory is 41 new public
heads (36 theorems and five definitions), plus 19 heads in those two existing
owners, plus 20 distinct reused declarations: **80 expected axiom records**.
Private proof helpers are audited through their public consumers.

Independent verification-source review passed for the unchanged shared
verifier API, exact reused names, imports, relative paths, workflow structure,
and inventory. Final checker SHA-256:
`4c19e0dd723772e1b960521107be4150d15b8079123c194c02f79f9961f599df`;
README SHA-256:
`ca5692fce348cfd9627b239247ca0809e797875e30336e409f3f06f9ad695403`;
workflow SHA-256:
`f436d3ef4a83380fe2ab1277b50c30f70c0137daf12dcbd5507359523aaba247`.
The workflow adds five identified upstream trigger paths alongside the
selected owners and controls. The filter is still a bounded dependency
filter, not a claim to cover every transitive project source change.

At integration, no compiler or axiom audit had accepted these new sources.
The successful preceding static checks and hook executions belong to the
parent/child repair snapshots; this packet requires its own fresh checks.

## Independent static validation

Run 001 passed all six maintained gates on the three new owners. Strict
proof proxy, semantic vacuity, semantic content, strict OpenGauss screening,
strict refutation, and static GATE_4 all returned zero. Semantic-content
findings and screener traps were zero. Three nonblocking lexical warnings
concern the two normalized generator representation readouts and the ordered
Born-product definition expansion; no mathematical conclusion is assumed
by those readouts.

The independent inventory confirmed 60 owner heads plus 20 reused
declarations: 80 expected and zero observed axiom records. Checker AST and
shared-verifier API inspection, workflow YAML, six shell blocks, and two
embedded Python AST checks passed. The executable workflow logic matches the
parent after packet-name substitution, including the prohibition on PR cache
saves. All eight staged/worktree files and selected controls matched the
frozen baseline during validation. The raw intake matched the uploaded bytes
and SHA-256 exactly.

Report SHA-256:
`b975077d5ede589396fe0113c8e417ef390ac2d11bc6bac4bc1e1be989fc3a74`.
This is a static PASS with kernel acceptance pending. No compiler ran in
this lane. The selected proof bodies still require fresh Lean elaboration
and the complete axiom audit before mathematical acceptance is recorded.


## Dependency compiler repairs incorporated after publication

This update incorporates child PR #447 at
`44b14b28a17a93161d8b112867bb5e0dc393207a`, tree
`7f277211609e3ff8daf38f962b53374920f7ac2f`, including parent PR #441 at
`a2571e4494c0d1598a881491fe7b734f6b896f1d`. The ordinary merge preserves
all published histories. The three new null/Born/volume owners, the raw
intake, the verifier, and its workflow are byte-identical to this PR's
initial reviewed publication.

The completed parent CI built the norm, Witt, and full-Cl(4,3) noninjectivity
owners. Its remaining determinant typing/rewrite diagnostics were repaired
in the parent. The completed child CI built infinitesimal triality, then
reported concrete coordinate-normalization goals in the derivation and
faithfulness owners. The child now contains independently reviewed repairs
for those exact goals, with all six scoped static gates and its actual
pre-commit hook passing. All public statements and declaration counts are
unchanged. Exact compiler logs, source hashes, and receipts are preserved
in the respective parent and child contracts.

These build results concern their recorded revisions. Fresh compiler and
axiom acceptance of the repaired dependencies and this null/Born/volume
packet remain pending. This packet still selects 80 expected axiom records;
zero complete-packet axiom records have been observed. The new owners'
previously recorded source/static reviews are unchanged by this merge.


## Targeted finite-vector projection normalization

The completed dependency run `45412837118` exposed nested `Matrix.vecHead`
and `Matrix.vecTail` applications to scalar multiples of coordinate vectors
in the concrete derivation proofs. A bounded review for that exact pattern
found the same mechanism in the two private sparse-product helpers of
`Canonical.ZornVolumeAction`: their inner native products contain terms such
as `z.b • Pi.single 2 1`, consumed by further dot/cross products.

The correction adds only `Matrix.vecHead` and `Matrix.vecTail` to the two
existing simplification lists. Root prepared the isolated correction and
`audit_math` independently approved its exact source delta. The readouts
reduce to coordinate application and successor composition in the pinned
Mathlib definitions. This is a source-supported normalization repair based
on an analogous observed failure, not a claimed compiler result for the
volume owner. Its four public statements, private helper statements,
imports, signs, and declaration counts are unchanged.

The new volume-owner SHA-256 is
`649612bce0b75345d18e05ff43cdaed7668fd06f7f17a860ee53c720b476bbac`.
The targeted checks of the null-kernel and Born-coordinate owners found no
supported repetition of the three investigated normalization patterns;
those files remain byte-identical to their original reviewed sources.

### Local runtime and checkout recovery

The guarded single-file local launch used the pinned `lake env lean -j1
-M768` route after the maintained lock became available. Lake exited with
SIGKILL before returning a Lean diagnostic. Package postflight checks
passed, but the executor connection then failed and its temporary checkout
and receipts were lost. The old observer's final exit and configuration
restoration could not be certified; no theorem acceptance is inferred.

A fresh ordinary checkout was recovered from published head
`8a16f056b5f2f13e01b942ff8d10b234e0498114`, tree
`ae130e76e0db576309a037dbdb199c1d594ae92d`. It was verified clean, with the
published configuration bytes and tracked pre-commit hook restored. No
local compiler retry is part of this update. Fresh kernel and axiom
acceptance remain pending, with 80 expected and zero observed complete-packet
axiom records.


### Static receipt for projection normalization

All six maintained gates scoped to `Canonical.ZornVolumeAction` returned
exit 0, with zero vacuity warnings, zero semantic-content findings, and zero
OpenGauss traps. Independent comparison confirmed that removing only the
two added definition names reproduces the preceding source byte-for-byte;
all declarations, statements, imports, and other proof bytes are preserved.
The two staged files and selected controls stayed unchanged during the run.
The independent inventory remains 60 owner heads plus 20 reused declarations:
80 expected axiom records, zero observed. This static run launched no Lean
compiler and does not certify kernel acceptance. Report SHA-256:
`8721927059ef27a8a0c74d1383a52a65de6c67aed97c205729b94e9607c5aa18`.
