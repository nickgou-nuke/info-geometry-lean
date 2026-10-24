# PR #205: mathematical scope and owner-reuse review

Task #18, reviewer `theorem_scope_review`, 2026-10-24.

**Recommendation: approve the algebraic scope with a minor owner-reuse nit, conditional on the parent's exact-source-closure compilation and axiom verification.** No mathematical correctness blocker was found by this source review. No compiler, build, test, gate, remote comment, commit, branch operation, or existing-file edit was performed. This report is not a kernel acceptance receipt.

## Provenance and review boundary

- Exact PR head: `ea08baa1649c9eeaf45638d6e7edef2f971ad1be`.
- Intended base, inspected directly through local Git objects: `21189e55133ed207043f2f05e37aa52d1fc8a9f5`.
- Exact added sources read in full: the five Lean files under `/tmp/pr205-review-ea08baa/lean/InfoGeometry/` and `docs/PEIRCE_WEYL_TRACE_CONTRACT.md`.
- Download metadata read: `/tmp/pr205-files.json`. Local `git hash-object` values for all five reviewed Lean files match those metadata blob IDs; details below.
- Current shared checkout HEAD is `d716c2504a4cf21015982248a0860644904239ec`, with substantial uncommitted shared work. It is **not** the PR base. Reuse findings below distinguish these contexts.
- Repository routing and protected-source/no-concurrent-build rules were already read for this session and retained. Only source reading, searches, hashes and the mandated staging were used here.

This PR now expressly targets algebraic MP/Hodge supports, ambient units, density/trace equations and native Jordan multiplication endomorphisms. Earlier criticism of purported geometric or analytic completion does not apply to the expressly excluded claims. It contains no TypedArchetype schedule whose interpretation needs to be audited.

## Findings, ordered by significance

### 1. Minor base-reuse nit: `skew_square` reproves the imported owner theorem

**Location:** `Core/PeirceWeylUnits.lean:60–66`.

`InfoGeometry.Core.PeirceWeylUnits.skew_square h hd` has precisely the already available conclusion and hypotheses of:

```lean
InfoGeometry.Core.DiracSuperalgebra.majoranaMinus_sq h hd
```

The base owner at `Core/DiracSuperalgebra.lean:402–412` proves `majoranaMinus d b * majoranaMinus d b = -activeSupport d b` from the same MP witness and square-zero premise. It is already imported by the PR's line 6, and its base file is byte-identical to the shared checkout version read here.

**Suggested smallest change:** replace the expansion proof by the existing theorem, or use the owner theorem directly at downstream calls. No new lemma or dependency is needed. This is maintenance duplication, not a false statement or semantic blocker. A compatibility wrapper, if deliberately retained, should forward rather than reprove.

### 2. The suggested `commutator_apply` duplication is not an exact-base defect

**Location:** `Core/JordanMultiplicationClosure.lean:28–35`.

Current shared `Core/JordanAssociatorRing.lean:125–130` contains `InfoGeometry.Core.JordanAssociator.symm_operator_commutator`, and the PR's `commutator_apply` could directly use it after its `change` line on that checkout. **However, the exact base's entire JordanAssociatorRing file is only 50 lines and does not contain that declaration.** Reading the base blob and a base `git grep` confirms this; current shared additions account for 146 extra lines.

The base does contain `symm_associator_eq_double_commutator`, which the PR explicitly reuses in `associator_orientation` at lines 38–43. Thus do not request a direct call to a nonexistent base declaration as an immediate prerequisite for this PR. A subsequent integration into the expanded shared owner should make `commutator_apply` forward to `symm_operator_commutator`, but this is concurrent integration cleanup, not an imported-base theorem being ignored.

### 3. No scope/vacuity blocker in the new synthesis

**Locations:** `Canonical/PeirceWeylSynthesis.lean:28–50`; contract sections “New theorem chain” and “Corrections and qualifications”.

The master theorem is a conjunction of concrete propositions over one carrier, with an actual MP witness and cyclic linear map as explicit hypotheses. It does not assume its full conclusion or a bespoke structure that simply stores the desired new laws. `SquareZeroChiralHodge d b` is an existing owner predicate whose actual conjunction and proof were read; the PR obtains it from the established MP decomposition theorem rather than treating it as a new hypothesis.

The master deliberately selects one directed weighted trace law and the sixth power, while helper modules prove both trace directions, both inverse equations, all four Weyl conjugation equations, and the sixth-root polynomial/cubic law. This is accurately described as a synthesis, not a claim that every helper conclusion is literally a conjunct of the master. No hidden strengthening or change of carrier was found.

## Mathematical checks and strengths, with exact lines

Use `P=d*b`, `Q=b*d`, `E=P+Q`, `H=1-P-Q`, `J=d-b`, `T=-Q+d-b`. These are shorthand for the actual imported definitions, not replacement carriers.

### A. Actual MP support foundation, not a proxy predicate

The base definition `InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse d b` consists of:

```text
d*b*d=d; b*d*b=b; star(d*b)=d*b; star(b*d)=b*d.
```

`Singular/SquareZeroMoorePenrose.lean:31–50` derives reverse support orthogonality by applying star to `(b*d)*(d*b)=0`, and then derives `b*b=0`. Therefore the PR need not add an independent `b²=0` hypothesis. This derivation is valid in an arbitrary associative star ring; no positivity or Hilbert-space existence theorem is silently used.

The PR reuses `SquareZeroChiralHodge`, `harmonicSupport_*`, `partial_matrix_unit_identities`, `activeSupport_identities`, and `harmonicSupport_star`. The relevant imported definitions/proofs were traced. These base support files are unchanged relative to the shared checkout, as confirmed by `git diff --quiet` against the exact base.

Requiring an MP witness is stronger than requiring a ring-level square-zero reflexive pair, but it is a deliberate owner-aligned API restriction, not a mathematical error or an inverse-existence claim. In this API it also produces the reverse square-zero law and self-adjoint supports. No `b=star d` claim appears.

### B. Ambient Weyl unit and proper support

**`Core/PeirceWeylUnits.lean:25–35, 40–117`.**

- `unipotent_triple` correctly needs only `d²=0` and `dbd=d`, and omits the star hypothesis. Expanding `(1+d)(1-b)(1+d)` leaves `1-db-bd+d-b`, exactly `H+J`.
- `harmonic_skew_zero` uses both annihilation orders, not a commutativity shortcut.
- `weyl_inverse_products` proves **both** `(H+J)(H-J)=1` and `(H-J)(H+J)=1`. `weylUnit` is an actual `Aˣ` with those fields, not merely an expression named inverse.
- `weyl_square` gives `H-E`; `weyl_fourth` uses `E²=E` to square `1-2E` to one without division by two. The result is an exponent-dividing-four law, correctly not exact order four.
- `weyl_conjugation` has the correct signs: `P↦Q`, `Q↦P`, `d↦-b`, `b↦-d`. The intermediate left/right support reductions in lines 118–147 agree with the matrix-unit table. The inverse used in the synthesis is definitionally the `weylInverse` supplied to the native unit.

### C. Supported cyclotomic identities

**`Core/PeirceWeylUnits.lean:149–223`.**

- `thirdRoot_square`: `T²=-P-d+b`; adding `T+E` cancels termwise.
- `thirdRoot_cube`: multiplying that quadratic reduction by `T` gives `P+Q=E`, using `PQ=0`, the absorption laws and both square-zero equations.
- `sixthRoot_laws`: for `-T`, the polynomial is `t²-t+E`, the cube is `-E`, and the sixth power is `E`. Parity/sign conventions are consistent.
- `cyclotomic_pair_recovers_transvection` uses **negative** skew generator: `(-J)T=E+d`. This sign matches the integral matrix witness.

These statements do not require characteristic zero, invertibility of 2 or 3, nonzero support, or exact multiplicative orders. In characteristic two signs can coincide; the displayed equations still make sense. The global zero pair is permitted and gives `E=0`, `H=1`, `w=1`; this is an appropriate degenerate case, not a contradiction to an unclaimed exact-order theorem. The active-root constant is never silently replaced by ambient one.

### D. Arbitrary weights and a genuinely used cyclic functional

**`Core/PeirceDensityIntertwining.lean:25–100`.**

The chosen ordering `ρ=uQ+vP` yields:

```text
ρd=vd,  dρ=ud,  ρb=ub,  bρ=vb.
```

`density_actions` obtains all four from the imported partial matrix-unit identities. `density_intertwining` cross-multiplies using commuting central scalars, so zero or noninvertible weights are not excluded. `squared_density_intertwining` is an honest specialization `u↦u², v↦v²`, not a positivity assertion.

`weighted_trace_of_intertwining` needs no star: it multiplies the given cross-intertwining equation on the right by `y`, applies the linear functional, and uses cyclicity on `x*(ρ*y)`. The resulting direction is correctly

```text
u τ(ρ(xy)) = v τ(ρ(yx)).
```

Both generator cases in `density_trace_boundary` use the proper coefficient ordering. `density_harmonic_annihilation` correctly shows both products with `H` vanish; it makes no ambient density-invertibility claim.

The hypotheses allow the zero trace and degenerate pair, but the theorem universally quantifies over all cyclic linear maps and all valid pairs; it does not select zero to discharge a purported nonzero theorem. Noncommuting witnesses are provided separately. Optional future packaging of `weightedTrace τ ρ` as a linear map may improve convenience, but its current scalar evaluation definition is exactly what the theorem needs.

### E. Native Jordan operators, correct normalization and bracket order

**`Core/JordanMultiplicationClosure.lean:22–64`.**

`jordanLeft s` is a native `Module.End R A` with action `sx+xs`, without a factor of one half. Native endomorphism multiplication composes in the order used, so `[J_s,J_t]x = [[s,t],x]`. `associator_orientation` gives the same value for `assoc(t,x,s)`; its reduction through the base associator owner has the correct sign. `commutator_leibniz` proves the associative derivation law of that resulting inner action, not an unsupported classification or a claim that every Jordan left multiplier is itself a derivation.

The base also has `Core/JordanPeirceDecomposition.jordanLeft`, but that is **normalized** by `1/2` and specialized to `Algebra ℝ A` (read lines 15–27). It is not a drop-in replacement for this division-free arbitrary-commutative-base API.

`trace_adjoint_identity` cancels to `τ(l(ξx)-(ξx)l)=0`. It needs only an additive cyclic trace; the proof does not infer dual-space identification or nondegeneracy.

### F. Concrete witnesses exercise the important boundaries

**`Canonical/PeirceWeylExamples.lean:21–69`.**

- `integral_pair` checks all four MP equations, not just two reflexive equations. `integral_noncommutative` excludes a commuting scalar toy realization.
- `integral_weyl_and_third` fixes the signs by explicit matrices `w=[[0,1],[-1,0]]`, `T=[[0,1],[-1,-1]]`, and `(-J)T=[[1,1],[0,1]]`.
- `grading_not_cyclotomic_two` checks `Γ+E≠0`; `source_jordan_sign_counterexample` and `square_zero_associator_nonzero` distinguish the corrected operator sign and the nonvanishing local associator.
- The 3×3 pair embeds the same two arrows with a third harmonic coordinate. Here `E=diag(1,1,0)`, `H=diag(0,0,1)`, `T³=E≠1`, but the completed Weyl element has fourth power one and fixes the third coordinate. `proper_corner_distinctions` therefore exercises precisely the ambient-versus-supported distinction rather than only the full-support 2×2 case.

All these are source-level checks of the stated formulas. Their `decide` proof terms and imports still require the parent's kernel verification; this worker did not run them. The `#check` commands are signature inspection commands, not substitutes for that verification.

## Exact-base reuse versus current integration overlap

A base tree lookup for the following four exact paths returned no entries: `Canonical/ReflexiveNilpotentFlows.lean`, `Canonical/ReflexiveWeightedTrace.lean`, `Canonical/IdempotentOrbitContracts.lean`, and `OperatorAlgebra/TracialCARDensity.lean`. They exist in the current shared checkout. This is a precise versioned path observation, not a claim that their mathematics has no alternative formulation anywhere in the base.

| PR surface | Current shared overlap read/searched | Correct integration interpretation |
|---|---|---|
| `weylElement`, `weylUnit`, inverse/fourth-power/conjugation laws | `InfoGeometry.Canonical.ReflexiveNilpotentFlows.weyl`, `weylUnit`, `weyl_mul_inverse`, `inverse_mul_weyl`, `weyl_fourth`, `weyl_swap_d`, `weyl_swap_B`, `weyl_swap_supports` | Same algebraic expressions up to additive reassociation, with weaker ring/reflexive hypotheses in the flow owner. If both branches land, specialize/reuse a common low-level owner rather than keep two expansion-proof families. Not a dependency this PR could have imported from its base. |
| `weighted_trace_of_intertwining` | `InfoGeometry.Canonical.ReflexiveNilpotentFlows.cyclic_weighted_balance`; directed support consumers in `ReflexiveWeightedTrace` | Same generic cyclic transport mechanism after unfolding `weightedTrace`. A good later deduplication target. The PR's arbitrary-weight density API is useful beyond squared parameters. |
| `cyclotomic_pair_recovers_transvection` | `InfoGeometry.Canonical.IdempotentOrbitContracts.cyclotomic_pair_recovers_transvection`; also `completeCornerUnit` | Exact expression-level overlap under weaker ring premises. Acknowledge concurrent overlap, not a false novelty accusation at the pinned base. |
| Density actions and trace boundaries | `InfoGeometry.OperatorAlgebra.TracialCARDensity.density_mul_ann`, `ann_mul_density`, `density_mul_cre`, `cre_mul_density`, `eigenproductKMS`, `annihilatorKMS`, `creatorKMS` | Related but not identical domains. Native CAR assumes `db+bd=1`; PR MP pairs may have **proper** support. Do not replace the PR with a full-support CAR theorem without a genuine corner map/structure. The general cyclic transport lemma is the straightforward reuse target. |
| Jordan operator commutator | `InfoGeometry.Core.JordanAssociator.symm_operator_commutator` in current expanded owner | Direct forwarding is appropriate after integration. It was absent from the exact base, as documented above. |

For future consolidation, prefer moving/reusing genuinely low-level algebra at the Core owner and having Canonical consumers specialize it; do not add a dependency cycle from this Core chain through the large current Canonical synthesis. No source refactor was attempted in this review.

## Acceptance decision

**Mathematical/source review: favorable.** The sign, scalar ordering, support constant, unit inverse, MP implications, and proper-support example align. The contract explicitly identifies its exclusions and does not assert an unobserved passing workflow. No missing mathematical hypothesis or unsatisfied nonvacuity requirement was found in the displayed statements.

**Before merge:** the parent must establish the exact five modules and unchanged import closure compile at the authenticated head with the expected foundational-axiom policy. This report provides no such run. Fix or record the small `skew_square` owner-reuse nit. Do not reject the PR on the superseded geometric rhetoric, require current-only `symm_operator_commutator` at the old base, or treat stronger MP hypotheses as a correctness bug.

**If merging with the current shared branch as well:** coordinate the overlaps listed above and use a fresh combined-source verification. Existing current-branch receipts cannot certify these PR additions, and an eventual PR-only receipt cannot certify a different combined tree.

## Hash record

All file paths in the first two tables are relative to `/tmp/pr205-review-ea08baa/`.

| Added file | Git blob ID, matching `/tmp/pr205-files.json` |
|---|---|
| `lean/InfoGeometry/Core/PeirceWeylUnits.lean` | `5e35eb4051102312e441186979db57cb36e821b4` |
| `lean/InfoGeometry/Core/PeirceDensityIntertwining.lean` | `10518d9fa5ff7bea08f51c6c657780e90c77875b` |
| `lean/InfoGeometry/Core/JordanMultiplicationClosure.lean` | `38998c233ad47c8c872c5bebcd1aa5fccf204748` |
| `lean/InfoGeometry/Canonical/PeirceWeylSynthesis.lean` | `db5d89b20c6b35656ecca7d84fdcfb5853cff7cc` |
| `lean/InfoGeometry/Canonical/PeirceWeylExamples.lean` | `f13c2096356027284028a9dcb61e280157175a4d` |

```text
SHA-256 reviewed additions:
5eb71d9838b58c30f823b772f6b6d953ee2f625e44089fe6586e15a113f97fe9  lean/InfoGeometry/Core/PeirceWeylUnits.lean
6fd7d487455bdc8bfec1a47c130cd61816eeb262bc8c8f6a3daa3e0112486095  lean/InfoGeometry/Core/PeirceDensityIntertwining.lean
7a4bbf9a9c072f181b5fed9efc9e6fed3b4d6120d48f4435292001d0008cb5ba  lean/InfoGeometry/Core/JordanMultiplicationClosure.lean
d305cc810f13a28520975f492a708bbeb1a51e69cf065fbe9a4c4fea9502a208  lean/InfoGeometry/Canonical/PeirceWeylSynthesis.lean
e0efd82ddb23726181a1007a421a75ee993af8e19133e960c3de4a1a697f24b2  lean/InfoGeometry/Canonical/PeirceWeylExamples.lean
48ec84399c3689358ace4cb5b06cd18841b1ff86313a88089c07ab3eee30ffbc  docs/PEIRCE_WEYL_TRACE_CONTRACT.md

Exact-base JordanAssociatorRing SHA-256:
9020f176054a171bc54c677b47aa1eaa5bd7cf1140fa37fdd35d87e799ee3fc2

Current shared comparison snapshot, paths relative to lean/InfoGeometry/:
40c319d2ee5297e756a25d597118a49f7f65c95bdf8ca9bf4b0d5d064825310a  Canonical/ReflexiveNilpotentFlows.lean
a463ca6d1d06710160a5e573e46d01b1cbfb6c9ea8a2d77b0ef1592dee1676da  Canonical/ReflexiveWeightedTrace.lean
342ecc89d74e977ccf6d4ae6b4ccd1ed8c94e20e1f30762723a14d250ebbfad7  Canonical/IdempotentOrbitContracts.lean
6734a0e8dfeca118bfded0a477c4bc85873bee401db8ab1e3a70c3b31124af16  OperatorAlgebra/TracialCARDensity.lean
10e0b1f9b942ab7cbb56f2fdf602cbeb56db9cd15eeec53e03bac6e2912c66c3  Core/JordanAssociatorRing.lean
a0fba78ffa87e8d4ab1703f936d63631351b9353a8fbe8d8f71e4266434629c3  Core/DiracSuperalgebra.lean
```

Base Git blobs for imported support owners read (unchanged relative to the shared checkout at review): `Core/DiracSuperalgebra` = `170ae640fe79a0c06eab7cdce7fbbc108dfe4339`; `Singular/MoorePenrose` = `b97bcd4da2e93b0795a03439830b7e28ee480cd3`; `Singular/SquareZeroChiralHodge` = `1d4bf9d4c8bcd1f2c6e68a56777b3b6d024d9d2a`; `Singular/SquareZeroMoorePenrose` = `2b557448b3728374024fbe1b5692cef230ebbaac`. Base `Core/JordanAssociatorRing` blob = `c244dfdeb65d0531a5bc6acfc73b5e52f047a718`.
