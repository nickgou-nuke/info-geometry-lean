# Exceptional CFSG proof-port status

This ledger separates external theorem coverage from what is currently
available through the repository's root-pinned local API. The external CFSG
submodule is at `69cb972f587a3ecc035e092253167ff2e303c962` and pins Lean
`v4.35.0-rc3` plus Mathlib `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`.
The root remains on Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The rows below therefore do not
imply that external modules are root-importable or kernel-checked under the
root toolchain.

Latest verification, 2026-10-30: the public
`InfoGeometry.Exceptional.CFSGPort.All` umbrella passes with 8,969 jobs.
`CurtisTitsRankOneBruhat.lean` now proves Weyl–torus interchange, the nonzero
root/Weyl reduction, stability of both Bruhat cells under Weyl and
negative-root multiplication, and `OperatorRankOneRels.mem_bruhat`: every
element of the actual rank-one root-module operator subgroup has one of the
two Bruhat forms. The concrete `operatorRankOneRels` instance was separately
elaborated against this theorem. Both the theorem and the instance depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

The same module now exports `operatorRankOne_bruhat`, in the external
`SteinbergExtras.rankOne_bruhat` factor order (`h * u` or `u * n * h * v`),
and `adjointGroup_rankOne_bruhat`, with all factors inside the actual adjoint
group and membership in its restricted root/torus subgroups. Both construct
their witnesses from the local operator decomposition; neither assumes the
factorization as an input. The public umbrella passes again with 8,969 jobs.

This supersedes the historical entries below that list rank-one two-cell
coverage as open. Assembly of the full external `SteinbergExtras` and
`BruhatExtras` interfaces, higher-rank arguments, and exceptional-family
simplicity remain unfinished. Existing warnings in imported modules remain.

The current local Suzuki work was checked through
`InfoGeometry.Exceptional.CFSGPort.All` (8,967 jobs, rechecked 2026-10-29) and the repository
entrypoint `InfoGeometry.All` (28,133 jobs, rechecked 2026-10-29). Both builds passed with existing
warnings. The latter's audit target reports no declarations depending on
`sorryAx`; it separately reports 303 generated explicit axiom constants from
other modules, so the full repository is not represented as axiom-clean by
this targeted verification.

On 2026-10-30, the current `InfoGeometry.Exceptional.CFSGPort.All` import
surface rebuilt successfully through the shared locked-build wrapper (8,968
jobs, exit code 0). This confirms the local API and its current import closure;
it does not establish any of the family-specific exceptional simplicity
theorems listed below.

On 2026-10-30, `InfoGeometry.Exceptional.CFSGPort.ExceptionalModelSimplicity`
rebuilt successfully through the locked wrapper (8,952 jobs, exit code 0)
after correcting `suzukiSGL_inv` in `ExceptionalCatalog.lean`. Its
characteristic-two parameter cancellation now proves equality of the
Suzuki inverse product with the zero-parameter operator by transporting the
parameter-pair equality through the operator parameterization. This verifies
the local Suzuki root-operator inverse formula and imported model adapter;
existing linter warnings remain, and this is not a Suzuki simplicity proof.

A fresh build of the complete `InfoGeometry.Exceptional.CFSGPort.All` umbrella
also passed on 2026-10-30 (8,968 jobs, exit code 0), including the current
`SuzukiOvoid.lean` source. This verifies the Suzuki upper-root subgroup's
parameter-range description, bijective parameterization, cardinality, and
solvability theorem on the actual general-linear operator carrier.

The Suzuki operator port now proves the torus conjugation law on the full
four-dimensional general-linear carrier, torus normalization of the upper-root
subgroup, normality of that subgroup in the generated root–torus subgroup, and
solvability of the root–torus subgroup by its solvable normal root subgroup and
abelian torus quotient. The root/Weyl subgroup's conditional two-transitivity
result also transfers to the full upper-orientation Suzuki operator group by
the proved subgroup inclusion. The focused locked owner check for
`SuzukiOvoid.lean` passed on 2026-10-30 after these additions. This matches
the solvable-stabilizer input shape in external Huppert–Blackburn XI.3.6, but
the local result is still only about the generated root–torus candidate:
equality with the full ovoid point stabilizer and perfectness of the full
Suzuki group remain unproved. Thus no local Suzuki simplicity theorem is
claimed yet. The updated public `InfoGeometry.Exceptional.CFSGPort.All`
umbrella then passed its locked build on 2026-10-30 (8,990 jobs, exit code 0).

The repository umbrella `InfoGeometry.All` then passed its locked build on
2026-10-30 (28,246 jobs, exit code 0), so the current root import closure
including Cantor and exceptional CFSG ports compiles together. Its audit target
reports zero declarations depending on `sorryAx` and 303 generated explicit
axiom constants; the repository is not thereby represented as axiom-clean.

The external `CFSG.LieType.Ree.suzuki_torus_identities` torus section is also
being ported locally. `zpow_two_pow_eq`, `suzukiD_eq`, `suzukiD_mul`, and
`suzukiD_one` now compile in `ExceptionalCatalog.lean`; the focused locked
target passed on 2026-10-30 (8,947 jobs, exit code 0). These identities fix the
local diagonal-weight convention needed for the still-open torus conjugation
formula on the transpose-presentation upper-root operators.

The independent Cantor simple-group port is now rechecked through
`InfoGeometry.Cantor.All`: the locked build completed successfully (9,001
jobs, exit code 0) on 2026-10-29. The owner
`Cantor/SimpleCantorPermutationGroup.lean` transports the OAI twisted
Brin--Thompson simple group along a bijection of its binary-stream carrier to
the repository's `CantorWord`, then proves simplicity by group equivalence.
`Cantor/SimpleCantorOperatorGroup.lean` faithfully represents that same group
by units in `Module.End ℝ (CantorWord → ℝ)` and transports simplicity to the
operator image. This is the local, noncommutative operator-carrier simplicity
result available from an external reference. It is distinct from the
Clifford-Markov channel and does not assert that the Markov operators equal
the simple permutation/operator group.

The additional OAI simple amenable group now has a repo-owned witness theorem
at `InfoGeometry.GroupTheory.SimpleAmenableWitness` on the actual
`polygonAlternatingGroup a 206` subgroup carrier. It extracts the infinite,
simple, Følner-amenable stage from `fixed_track_polygon_progress` and ports
the finite-presentation conclusion through its central-cover and homology
inputs. The focused locked build passed (9,474 jobs, exit code 0), and the
aggregate `InfoGeometry.All` build passed after adding this adapter (28,137
jobs, exit code 0) on 2026-10-29.

That witness now also has a faithful operator-unit realization on the same
track-point carrier: `polygonOperatorGroup` is the image in
`(Module.End ℝ (TrackPoint a 206 → ℝ))ˣ`,
`polygonOperatorUnitRep_injective` proves faithfulness, and
`polygonOperatorGroup_simple` transports simplicity through the group
equivalence. `polygonGroup_exists_noncommuting_pair` proves that the source
group is noncommutative: otherwise commutative simplicity would make it finite,
contradicting its proved infinitude. `polygonOperatorGroup_exists_noncommuting_pair`
transfers the witness to the operator-unit subgroup. The focused owner build
and the 28,137-job aggregate build both passed after this extension. This is
the endomorphism-algebra carrier; the separate Clifford-Markov operators are
not identified with this permutation group.

## Current root-port verification boundary (2026-10-29)

`ChevalleyBorelIntersection.lean` is a local operator-carrier adaptation of
the torus/positive-unipotent intersection lemma. Its generator case now proves
`torusElt t⁻¹ = (torusElt t)⁻¹` from the local `torusElt_mul` and
`torusElt_one` identities. The inverse-of-product case uses `mul_inv_rev` and
the reversed composition order. The owner passed `run_locked_lean.py`, and
`InfoGeometry.Exceptional.CFSGPort.All` built successfully with the module
imported (8,963 jobs). An earlier Lake attempt against the faulty generator
proof failed; that failure is superseded by the successful direct kernel check
and umbrella build.

`operatorBorelSubgroup_isSolvable` now proves solvability of the Borel subgroup
on the actual root-module endomorphism-unit carrier. The proof makes the
positive unipotent subgroup normal inside the torus/unipotent join, identifies
the quotient as a surjective image of the commuting root torus, and combines
the two solvable pieces. The focused locked build
`InfoGeometry.Exceptional.CFSGPort.ChevalleyBorelIntersection` passed on
2026-10-30 (8,950 jobs, exit code 0). This supplies the solvable-Borel input
shape for the rank-one simplicity route; the remaining family-specific
Bruhat, generation, and conjugation hypotheses are not thereby discharged.

The current staged tree adds `CurtisTitsRankOne.lean` to that umbrella. It
defines noncommutative operator-unit subgroups for the simple Weyl operators,
rank-one root operators, and simple-root torus. The G₂ theorem
`torusElt_eq_one_of_torusElt_G2_eq`, generic generated-torus membership theorem
`exists_torusElt_eq_of_mem_simpleRootTorusSubgroup`, and
`simpleRootTorusSubgroup_iSupIndep_G2` are kernel-checked: the focused locked
build `InfoGeometry.Exceptional.CFSGPort.CurtisTitsRankOne` completed
successfully (8,947 jobs, exit code 0) on 2026-10-29. The independence proof
uses the generic parameter-extraction theorem and shows the two operator-torus
subgroups intersect trivially. This is an operator-level Curtis--Tits input,
not an exceptional-family simplicity proof. The umbrella target
`InfoGeometry.Exceptional.CFSGPort.All` then rebuilt successfully with this
module in its public import surface (8,967 jobs, exit code 0) on the same date.

On 2026-10-30, the operator rank-one owner was extended with an explicit local
`OperatorRankOneRels` instance, the rank-one `w(t)` and `h(t)` elements inside
the operator subgroup, and the identification of `h(t)` with `torusElt`. The
`h` parameter multiplication and both positive/negative simple-root torus
conjugation laws were checked by the focused locked target
`InfoGeometry.Exceptional.CFSGPort.CurtisTitsRankOne` (8,948 jobs, exit code
0). This carries the algebraic rank-one inputs on the actual endomorphism-unit
group. The new two-cell Bruhat-set definition and identity-membership proof
are later staged additions and are not included in that build evidence yet;
Bruhat closure, the decomposition theorem, and exceptional simplicity remain
open.

`ChevalleyNormalizerTriviality.lean` now also proves
`eq_one_of_mem_normalizer_negSimpleRoot`: any element of a pinned simple-root
subgroup on the root-module endomorphism units that normalizes its opposite
simple-root subgroup is the identity. This closes the step from the external
`xUnit` parameter lemma to the arbitrary generated-root-subgroup form used by
the external `g2_eq_one_of_mem_normalizer` input. The focused locked build
`InfoGeometry.Exceptional.CFSGPort.ChevalleyNormalizerTriviality` passed on
2026-10-29 (8,944 jobs, exit code 0). The external `IsCTGroupDatum`, full
`SteinbergExtras`, `BruhatExtras`, and G₂ quasisimplicity arguments remain
unported; this lemma is one of their operator-level fields.

`adjointGroup_eq_one_of_mem_normalizer_negSimpleRoot` states this criterion on
the restricted root subgroup inside the local adjoint operator group and
converts its relative normalizer condition to the ambient endomorphism-unit
normalizer. It is kernel-checked by a successful focused locked build of
`InfoGeometry.Exceptional.CFSGPort.ChevalleyNormalizerTriviality` (8,944 jobs,
exit code 0) on 2026-10-29. This gives the external G₂ proof its normalizer
input on the matching local adjoint carrier, but does not establish the other
Curtis--Tits, Bruhat, or quasisimplicity hypotheses. The umbrella
`InfoGeometry.Exceptional.CFSGPort.All` also rebuilt successfully after this
exact carrier version (8,967 jobs, exit code 0).

`ChevalleyBorelIntersection.adjointGroup_borel_inf_negUnipotent` has been
added as the carrier restriction of the existing ambient operator Borel
intersection, matching the external `BruhatExtras` field. Its focused locked
build `InfoGeometry.Exceptional.CFSGPort.ChevalleyBorelIntersection` passed on
2026-10-29 (8,949 jobs, exit code 0). This checks the carrier restriction; it
does not construct the remaining `SteinbergExtras` fields or prove G₂
quasisimplicity. The umbrella target `InfoGeometry.Exceptional.CFSGPort.All`
also rebuilt successfully with this owner (8,967 jobs, exit code 0).

`ChevalleyBorelIntersection.adjointGroup_posUnipotent_inf_negUnipotent`
restricts the positive/negative root subgroup intersection to the local
adjoint operator group. This matches the carrier shape of
`SteinbergExtras.posPart_inf_negPart` after the external adjoint-group
identification. The focused locked build
`InfoGeometry.Exceptional.CFSGPort.ChevalleyBorelIntersection` passed on
2026-10-29 (8,949 jobs, exit code 0). It is a carrier restriction of the
existing triangularity theorem and does not discharge the missing ordered
root-product or Bruhat fields.

`Chevalley.rootSubgroup_ne_bot` proves every pinned root subgroup on the
endomorphism-unit carrier is nontrivial over a nontrivial coefficient ring,
using injectivity of the pinned parameter map. This supplies the local
`SteinbergExtras.ne_bot` field for any root. The focused locked build
`InfoGeometry.Exceptional.CFSGPort.ChevalleyRootGroups` passed on 2026-10-29
(8,943 jobs, exit code 0). The `InfoGeometry.Exceptional.CFSGPort.All`
umbrella also rebuilt successfully with this owner (8,967 jobs, exit code 0).

`Chevalley.rootSubgroup_two_smul_le` supplies the local operator-carrier form
of `SteinbergExtras.two_smul_le`. Its hypothesis that twice a root is a root
is impossible by the checked reduced-root certificates, so the inclusion is
proved by elimination on the actual root subgroup of endomorphism units. The
focused locked build `InfoGeometry.Exceptional.CFSGPort.CommutatorTorus`
passed on 2026-10-29 (8,947 jobs, exit code 0). This closes one additional
field of the external interface; commutator-in-open-cone, ordered root-product
injectivity, and rank-one Bruhat remain unported.

The root `CFSGPort.All` surface imports local model, root-group, perfectness,
quasisimple-transport, rank-one-criterion, Borel-intersection, and J₁
generator-order modules. It does not import the external CFSG family-simplicity modules. The
local J₁ port proves the seed orders 2, 3, and 7 and that the two seed
operators do not commute; the external primitive 1,540-point action
certificate and its stabilizer/orbit proof have not been ported as a local
J₁ simplicity theorem. Likewise, the local exceptional adapters still leave
family-specific normal-subgroup/Bruhat inputs explicit. These are remaining
proof-port obligations, not root import successes.

The local M₁₁ permutation carrier now names the same two seed permutations as
the external CFSG `CFSG.Sporadic.Mathieu.m11gA` and `m11gB` definitions, and
`m11SeedA_order` and `m11SeedB_order` prove their orders are 2 and 4;
`m11Seed_noncommute` proves their noncommutation in the generated subgroup by
kernel reduction. The port also includes the generic
`closure_pair_eq_top_of_eq_closure` lemma from the external Mathieu proof and
its application `m11Seed_closure_eq_top`, so the local seed pair has the
required generation property on the subtype carrier. The carrier owner passed
the locked direct Lean check after these additions (exit code 0, 2026-10-30).
The same owner also proves `m11_finite` and `m11_nontrivial`, matching the
first two conjuncts of the external family theorem. These are carrier-level
results only. A previous local draft treated the SLP `[1,2,1,2,1,2]` as a
derived generator for a primitive-action criterion; that interpretation was
incorrect. In the external CFSG source the simplicity theorem uses the
original M₁₁ generators `m11a` and `m11b` together with a Mathieu-chain
certificate (`Certificate3120`), not a second generating pair. A local
permutation search confirms that pairing `m11b` with `(m11a*m11b)^3` generates
only 188 elements, so it cannot witness generation of M₁₁ (order 7,920). The
unsupported auxiliary-pair lemmas have been removed. Porting the actual proof
requires the checked chain data, its certificate interpretation, and the
primitive-action/coprime-orders argument; no local M₁₁ simplicity theorem or
external module import has been claimed.

The local `ExceptionalModelSimplicity.lean` now also contains the external
helper `pow_pow_card_sq`: for a finite field with cardinality `q ^ 2`, the
`q`-power Frobenius squares to the identity. The local port also includes
`two_mul_lt_ReeG2_parameter` and the generic `not_dvd_two_mul_of_goodChar`
bound from `ReeSmall.lean`. The latter is the arithmetic step used to show
that a Ree torus commutator acts nontrivially on a chosen root operator.
Both declarations kernel-check in the local pinned environment. The updated
`CFSGPort.All` build previously passed (8,964 jobs). These verified support
lemmas do not themselves prove ²E₆ or ²G₂ simplicity. The derived ²E₆
fixed-subgroup quasisimplicity proof and model equivalence, and the ²G₂
fixed-root quasisimplicity proof and model equivalence, remain open.

## External terminal theorem cross-check (2026-10-30)

The exceptional family boundary was checked against theorem statements in
the checked-out CFSG source, rather than inferred from file names. This is
the present local import/port map for its generic simplicity route:

| External CFSG owner and declaration | Actual external conclusion | Root-pinned local counterpart / remaining gap |
|---|---|---|
| `CFSG/LieType/TitsSimplicity/Simplicity.lean`: `isSimpleGroup_quotient_center_of_forall`, `isQuasisimple_of_forall`, `isSimpleGroup_quotient_center_of_isSolvable`, `isQuasisimple_of_isSolvable`, `isSimpleGroup_quotient_center`, `isQuasisimple` | Generic Tits-datum criterion: perfectness, indecomposable Cartan data, Bruhat extras, and root-group commutators imply simplicity of the center quotient or quasisimplicity of the covering group. | The abstract normal-subgroup-dichotomy transport exists in `CFSGPort/ExceptionalModelSimplicity.lean`; the rank-one criterion exists in `CFSGPort/RankOneSimplicity.lean`. These do not yet port the external `IsCTGroupDatum`, full `SteinbergExtras`, `BruhatExtras`, and `RootGroupCommutators` package on the local exceptional operator carrier. |
| `CFSG/LieType/Steinberg/TwistedE6/Clause0.lean`: `fixedGroup_isQuasisimple`, `fixedGroup_isQuasisimple_of_four_le_card` | Quasisimplicity of the twisted E₆ fixed subgroup, with the second theorem using the finite-field cardinality bound and classical SL₂ perfectness. | `ExceptionalModelSimplicity.lean` ports the field-cardinality Frobenius involution and a general twisted-model transport adapter, but not the local fixed-subgroup quasisimplicity proof or its operator-carrier root data. |
| `CFSG/LieType/Steinberg/TwistedD4/Quasisimple.lean`: `twistedGroup_isQuasisimple`, `twistedGroup_isQuasisimple_of_card`, `isQuasisimple_derived_twistedFixedGroup_D4` | Quasisimplicity of the twisted D₄ carrier and its derived fixed subgroup; the final declaration is the rank-one-twisted family input. | The local twisted model adapter transports a supplied quasisimple derived subgroup. The D₄ fixed-group construction, its actual root operators, and this family proof are not yet ported. |
| `CFSG/LieType/Steinberg/Exceptional/{Universal,TwistedE6}.lean` | The exceptional universal groups are instantiated by E₆, E₇, F₄, and E₈ root data; `twistedE6_conclusionA` proves a conclusion-A package for twisted E₆. These are root-datum/presentation inputs to the simplicity architecture, not themselves the missing local group-simplicity theorem. | The local catalog contains exceptional Chevalley operator models and theorem adapters, imported by `CFSGPort.All`; family-specific normal-subgroup dichotomies and a local transport of the external exceptional root-datum package remain open. |
| `CFSG/LieType/TitsSimplicity/Simplicity.lean`: `isSimpleGroup_quotient_center_of_isSolvable` and `isSimpleGroup_quotient_center` | Simplicity of the adjoint quotient from solvability of the positive unipotent subgroup or its root-commutator input. | Local `ChevalleyBorelIntersection.lean` proves solvability of the Borel on endomorphism units, and `CommutatorTorus.lean` proves perfectness of the exceptional adjoint carrier under stated field-size bounds. The decisive local normal-subgroup dichotomy/Bruhat proof is still absent; local theorems expose it as an explicit hypothesis. |

No external `CFSG.*` import has been added to the root import graph. The
external submodule uses Lean `v4.35.0-rc3` and Mathlib
`b63f6e8a68d220e3b3bc4f3792bb53650d375f24`; the root remains pinned to Lean
`v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The next
proof-port work must translate these terminal inputs onto existing local
operator carriers and prove compatibility there. This table is scoped to the
exceptional Tits/Steinberg files inspected above; it is not a complete
inventory of every finite simple group theorem in the external CFSG project.

The post-integration build of `InfoGeometry.All` initially failed in four
`Omega.Zeta` targets and `InfoGeometry.OperatorAlgebra.PeirceNambuGorkov`.
`PeirceNambuGorkov` now builds after correcting the coefficient in
`squareZeroPair_spin_mass_precession` from `4` to `2` and making the
Peirce-reflection theorem arguments explicit. The four `Omega.Zeta` owners
now build after removing an unsupported function-field Galois-group claim;
the actual geometric S₄ generation proof remains. The targeted builds of
`CFSGPort.All`, `ClNNPermutationSymmetry`, and the exceptional root-operator
Weyl owner pass. Subsequent full root builds pass for `InfoGeometry.All`
(28,100 jobs) and `InfoGeometry` (29,349 jobs), both exit code 0, including
the updated exceptional operator-Weyl imports.

## Repo-owned `IsSimpleGroup` source cross-check

The checked-out `lean/` tree currently has nine Lean owner files containing
the literal `IsSimpleGroup` (searched with `rg -l --glob '*.lean'
'IsSimpleGroup' lean`). This is an exact textual-source index, not a semantic
proof inventory: it can miss locally aliased predicates and it counts both
theorems and uses of assumptions. Reading the declarations in those owners
gives this classification:

| Owner | Locally proved simple-group content |
|---|---|
| `InfoGeometry/Cantor/SimpleCantorPermutationGroup.lean` | The transported Cantor permutation group is simple, using the imported twisted Brin/Thompson simplicity theorem. |
| `InfoGeometry/Cantor/SimpleCantorOperatorGroup.lean` | Its faithful endomorphism-unit image is simple by transport; this is an actual noncommutative operator group. |
| `InfoGeometry/GroupTheory/SimpleAmenableWitness.lean` | The polygon alternating group is simple and has a faithful simple image in endomorphism units; the owner also proves infinitude, amenability, and noncommutativity. |
| `InfoGeometry/Exceptional/CFSGPort/SimpleFamilyCatalog.lean` | Cyclic groups of prime order and alternating groups of degree at least five, transported across the model equivalences. |
| `InfoGeometry/Exceptional/CFSGPort/ClassicalSimpleFamilyCatalog.lean` | PSL₂ over fields of cardinality at least four, plus its local model transport. |
| `InfoGeometry/Exceptional/CFSGPort/PrimitiveCoprimeSimplicity.lean` | Generic criterion and J₁-shaped application boundary; family proof requires its primitive action and stabilizer hypotheses. |
| `InfoGeometry/Exceptional/CFSGPort/QuasisimpleTransport.lean` | Generic central-quotient and quasisimple transport criteria, not a named exceptional-family proof. |
| `InfoGeometry/Exceptional/CFSGPort/RankOneSimplicity.lean` | Generic rank-one criterion, conditional on Bruhat, solvability, and generation inputs. |
| `InfoGeometry/Exceptional/CFSGPort/ExceptionalModelSimplicity.lean` | Exceptional-family transport adapters; untwisted G₂/F₄/E₆/E₇/E₈, twisted ²E₆/³D₄, Ree/Tits, and Suzuki simplicity still require explicit family inputs. |

This local scan confirms two non-CFSG simple operator-group results and the
limited unconditional CFSG model families above. It does not turn the external
CFSG theorem owners into root imports; those remain tracked separately below.

## Exceptional simple-family theorem map

The external simplicity directory also exports lower-level results separate
from its `fam_*` catalog theorems. The following rows record the exceptional
and generic criteria traced so far:

| External declaration | Statement-level role | Local status |
|---|---|---|
| `isSimpleGroup_adjointQuotient_f4` | Proves simplicity of `AdjointQuotient .F4 K` from the external F₄ quasisimplicity theorem | `isSimpleGroup_adjointQuotient_of_normalDichotomy` now exposes the exact local quotient conclusion for any tag, given fieldwise perfectness and the central-or-total normal-subgroup dichotomy; F₄ inputs remain unproved locally |
| `isSimpleGroup_adjointQuotient_e8` | Proves simplicity of `AdjointQuotient .E8 K` from the external E₈ quasisimplicity theorem | Same conditional quotient adapter; E₈ family inputs remain unproved locally |
| `isQuasisimple_adjointGroup_e6` | Proves quasisimplicity of the finite-field adjoint E₆ group by a nontrivial isogeny quotient | No local family proof found; local `isQuasisimple_adjointGroup_of_normalDichotomy` requires a fieldwise perfectness and normal-subgroup dichotomy proof |
| `isQuasisimple_adjointGroup_e7` | Proves quasisimplicity of the finite-field adjoint E₇ group by a nontrivial isogeny quotient | No local family proof found; same generic conditional boundary |
| `isSimpleGroup_quotient_center_reeFixed_F4` in `ReeLargeModel.lean` | Proves simplicity of the central quotient of the large-Ree `F₄` fixed group from its perfectness and normal-subgroup analysis | Local `isSimpleGroup_of_ReeTitsRelationModel` is only a transport adapter; the fixed-group perfectness and normal-subgroup proof are not locally established |
| `isQuasisimple` in `TitsSimple.lean` | Proves quasisimplicity of the derived `F₄` Ree-fixed group when `Nat.card K = 2` | No matching local small-field derived-fixed-group theorem found; the local Tits model adapter leaves quasisimplicity as an input |
| `isQuasisimple_of_rankOne` and `isSimpleGroup_quotient_center_of_rankOne` in `RankOneQuasisimple.lean` and `RankOne.lean` | Generic Bruhat/perfectness/solvable-Borel criteria for quasisimplicity and central-quotient simplicity | `RankOneSimplicity.lean` ports the normal-core argument, the subgroup restriction form, and the quasisimplicity/quotient conclusions. Family-specific Bruhat, solvability, conjugation, and generation fields remain to be discharged |
| `isSimpleGroup_of_isPreprimitive_of_isSolvable_stabilizer` in `Primitive.lean` | Generic simplicity criterion from a faithful preprimitive action, solvable point stabilizer, and perfectness | Ported under the same theorem name in `PrimitiveCoprimeSimplicity.lean`; exceptional-family applications still need their action, stabilizer-solvability, and perfectness proofs |

These external declarations are proof targets, not root imports. The
root-owned family theorem adapters below preserve the conclusion shape but do
not discharge the listed fieldwise quasisimplicity inputs.

| Family | External source theorem | Local port boundary | Remaining proof debt |
|---|---|---|---|
| Untwisted `G₂` | `CFSG.LieType.Simplicity.fam_g2_simplicity` in `CFSG/LieType/Simplicity/Exceptional.lean` | `isSimpleGroup_of_G2Model_of_normalDichotomy`; local G₂ perfectness is used by `isQuasisimple_adjointGroup_G2_of_normalDichotomy`. `ChevalleyNormalizerTriviality.lean` now ports the actual root-module operator lemma corresponding to the `eq_one_of_mem_normalizer` field used by external `g2_steinbergExtras`. | Continue porting the complete external `g2_isCTGroupDatum`, `g2_steinbergExtras`, and `g2_bruhatExtras` interfaces to the local operator carrier, then discharge the generic Tits simplicity criterion using the existing root-commutator data, Cartan indecomposability, and perfectness. The new normalizer lemma is one field-level input; it does not construct the missing interfaces or prove G₂ simplicity. |
| Untwisted `F₄`, `E₆`, `E₇`, `E₈` | `fam_f4_simplicity`, `fam_e6_simplicity`, `fam_e7_simplicity`, `fam_e8_simplicity` in `Exceptional.lean` | `isSimpleGroup_of_untwistedChevalleyModel_of_normalDichotomy`, generic in the exceptional tag | Port the family quasisimplicity arguments and show they discharge the local perfectness/normal-dichotomy boundary. |
| Twisted `²E₆` | `fam_2e6_simplicity` in `Exceptional.lean` | `isSimpleGroup_of_twistedChevalleyModel` | Port quasisimplicity of the derived twisted fixed subgroup and its identification with the local model. |
| Triality `³D₄` | `fam_3d4_simplicity` in `TrialityD4.lean` | `isSimpleGroup_of_twistedChevalleyModel` | The external owner extracts `Nat.card K = (p ^ f)^3`, derives `2 ≤ p^f`, applies `isQuasisimple_derived_twistedFixedGroup_D4` to the Frobenius twist, then transports simplicity over the model equivalence. The local adapter already has the corresponding generic fixed-derived-subgroup hypothesis; the missing work is the D₄-specific quasisimplicity proof and proof that the local `TwistTag.D4` carrier is the same derived fixed subgroup. |
| Ree `²G₂` | `fam_2g2_simplicity` in `ReeSmall.lean` | `isSimpleGroup_of_ReeTitsRelationModel`; `two_mul_lt_ReeG2_parameter` and `not_dvd_two_mul_of_goodChar` port arithmetic inputs used by the external perfectness argument | Port the Ree fixed-root subgroup quasisimplicity argument and prove the local relation model equivalence. The arithmetic ports alone do not establish Ree perfectness or simplicity. |
| Ree `²F₄` | `fam_2f4_simplicity` in `ReeLargeModel.lean` | `isSimpleGroup_of_ReeTitsRelationModel` | Port the large Ree family proof and prove its hypotheses from the local model. |
| Tits group | `fam_tits_simplicity` and `fam_ree_tits_simplicity` in `TitsModel.lean` | `isSimpleGroup_of_ReeTitsRelationModel` | Port the Tits-specific derived subgroup simplicity input and establish the model equivalence. |
| Suzuki `²B₂` | `fam_2b2_simplicity` in `Suzuki.lean` | `isSimpleGroup_of_SuzukiExceptionalModel` | The local carrier acts by general linear operators on the four-dimensional module and proves `suzukiGroup_noncommuting_pair` from the `(1,0)` root operator and antidiagonal Weyl operator. `ExceptionalCatalog.lean` exposes `suzukiSGL`, the full root/torus/Weyl generator sets and their matrix subgroup, and proves `suzukiUpperMatrixGroup_inverseTranspose`, identifying upper-root and lower-root generator presentations by an actual group automorphism. It also ports the external diagonal torus weight formula and its multiplicative/identity laws as `suzukiD_eq`, `suzukiD_mul`, and `suzukiD_one`. `MatrixInverseTranspose.lean` locally ports the external GL inverse-transpose equivalence using Mathlib's transpose-to-opposite-ring equivalence and group inversion. `SuzukiOvoid.lean` defines `suzukiTorusOperator` on the same noncommutative linear carrier and proves its membership in both the full Suzuki matrix group and its endomorphism-operator image. `upperRootMatrixGroup_eq_paramRange`, `upperRootParamEquiv`, `upperRootMatrixGroup_card`, and `upperRootMatrixGroup_isSolvable` now establish that the upper-root operator subgroup is a finite 2-group and hence solvable. The generated `suzukiTorusOperatorGroup` is kernel-checked abelian and solvable, and `suzukiTorusOperatorGroup_map_le_suzukiGroup` places its operator image inside the full linear-operator group. `suzukiPointStabilizerOperatorGroup` joins this torus with the upper-root subgroup; `suzukiPointStabilizerOperatorGroup_le_stabilizer` proves this root-torus candidate fixes infinity in the actual projective action. The torus conjugation formula needed to prove solvability of the root-torus extension, and equality with the full point stabilizer, remain open. The kernel-checked `suzukiTorusOperator_smul_finite` and `suzukiTorusOperator_maps_ovoid` theorems prove its chart and ovoid actions. `suzukiUpperMatrixGroup_smul_mem_ovoid` lifts root, torus, and Weyl generator actions to the existing full upper-orientation Suzuki operator group, under the stated finite-field and Suzuki norm hypotheses. `rootWeylOperatorGroup_le_suzukiUpperMatrixGroup` embeds the noncommuting root/Weyl witness into the full group, and `suzukiUpperMatrixGroup_noncommuting_pair` proves the full operator group is noncommutative. The kernel-checked `rootWeylOperatorGroup_two_transitive_on_ovoid` proves two-transitivity for the root-plus-Weyl subgroup under the explicit field, automorphism, and norm-zero hypotheses. Solvability of the full point stabilizer, perfectness, and equivalence to the external `SuzukiMatrixGroup` remain open, so this does not yet give Suzuki simplicity. The root subgroup's separate noncommutativity result follows under the explicit nontriviality condition for the Tits automorphism. The carrier-orientation mismatch is resolved. |

### G₂ Tits criterion: local field coverage

The G₂ source route uses the external `SteinbergExtras` and `BruhatExtras`
structures before applying the Tits quasisimplicity criterion. A targeted
comparison of those structure fields with the current local owners gives the
following port status. “Local field lemma” means a result on the matching
noncommutative root-module operator carrier; it does not mean the external
structure has been assembled for that carrier.

| External field | Local source evidence | Status for assembling the G₂ criterion |
|---|---|---|
| `SteinbergExtras.ne_bot`, `two_smul_le` | `ChevalleyRootGroups.lean`: nontrivial pinned root subgroups and the reduced-root double-multiple result | Local field lemmas present. |
| `SteinbergExtras.prodInjective_pos`, `prodInjective_neg` | `ChevalleyProductInjectivity.lean`: positive- and negative-height product injectivity for the local pinned root groups | Local field lemmas present. |
| `SteinbergExtras.posPart_inf_negPart`, `torus_inf_posPart` | `ChevalleyBorelIntersection.lean`: positive/negative subgroup intersection and simple-root-torus/positive-subgroup intersection | Local intersection lemmas present. |
| `SteinbergExtras.eq_one_of_mem_normalizer` | `ChevalleyNormalizerTriviality.lean`: root-module operator normalizer criterion, including its adjoint-subgroup restriction | Local field lemma present. |
| `SteinbergExtras.torus_commute`, `torus_iSupIndep` | `CurtisTitsRankOne.lean`: commuting simple-root tori and independence; G₂ has its explicit Cartan calculation | Local G₂ field lemmas present. |
| `SteinbergExtras.commutator_mem` | External field requires commutators of independent root groups to lie in the subgroup generated by roots in their open cone | `ChevalleyRootGroupsTriangular.lean` proves `commutator_mem_posFiltration` and `posUnipotent_commutator_le_posFiltration_two` for the actual endomorphism-unit carrier. This only puts positive-unipotent commutators in a coarse triangular filtration; it does not give the open-cone subgroup containment or cover arbitrary independent roots. The sharper root-cone commutator formula remains an open port obligation. |
| `SteinbergExtras.rankOne_bruhat` | External field requires the two-cell factorization for every rank-one subgroup element | External `Adjoint/RankOne.lean` imports `PartBRankOne.lean` and certificates 113, 114, and 117. It identifies the rank-one carrier with a subgroup of `SL₂(K)` using `restrictEquiv`, obtains the two-cell split from `rankOneRels.bruhat` via `mem_bruhat`, then rewrites the torus and Weyl factors into the adjoint carrier. Locally, `CurtisTitsRankOneBruhat.lean` now proves `operatorRankOne_bruhat` on the subgroup generated by the actual positive and negative root operators and transports the factorization into the adjoint group. This closes the rank-one field at the local carrier level; constructing the external universal-root-datum package remains separate. The focused locked target passed on 2026-10-30 (8,949 jobs), and `InfoGeometry.Exceptional.CFSGPort.All` rebuilt on 2026-10-30 (8,988 jobs). |
| `BruhatExtras.borel_inf_negUnipotent` | `ChevalleyBorelIntersection.lean`: actual operator Borel subgroup has trivial intersection with the negative unipotent subgroup | Ambient operator-carrier lemma present; the local root datum and all `SteinbergExtras` fields still need to be assembled together. |

This comparison narrows the next G₂ work to concrete missing fields rather than
another generic transport adapter. It does not establish that the existing
field lemmas have matching definitions or implicit hypotheses for direct
structure construction; that assembly still requires a root-pinned Lean check
under the repository build lock. The external definitions are in
`CFSG/LieType/Steinberg/Extras.lean` and
`CFSG/LieType/Steinberg/BruhatWeyl.lean`; the G₂ instances are assembled in
`CFSG/LieType/Steinberg/G2/Extras.lean`.

The Suzuki source route is particularly concrete: external
`fam_2b2_simplicity` first transports a `SuzukiModel` to the native
`SuzukiMatrixGroup`, then applies
`CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6`. The local operator port
now proves generator actions on the projective ovoid, including its torus,
but it does not yet identify the local upper-orientation operator group with
the theorem's `SuzukiMatrixGroup` carrier or discharge Huppert–Blackburn's
hypotheses. The ovoid action and noncommuting pair are structural inputs, not
a substitute for that imported simplicity theorem.

The local `SuzukiOvoid.lean` owner now proves
`rootWeylOperatorGroup_exists_map_ovoid_to_infinity`: under characteristic
two and the stated Suzuki automorphism identities, every point in the ovoid
can be sent to the distinguished point at infinity by an element of the
local root-plus-Weyl operator subgroup. The proof uses the upper-root
translation formula to take each finite chart point to `(0,0)`, followed by
the Weyl operator. The derived theorem
`rootWeylOperatorGroup_transitive_on_ovoid` composes the point transporters
and proves transitivity of the local operator subgroup on the ovoid. The
owner also proves `upperRootMatrixGroup_transitive_on_finite_chart`, by
choosing the two upper-root parameters explicitly to send any finite chart
point to any other. The focused locked build passed on 2026-10-30 (8,948
jobs), and the public `InfoGeometry.Exceptional.CFSGPort.All` umbrella
rebuilt successfully with these results in its import closure (8,968 jobs).
The root-plus-Weyl operator group now also has a kernel-checked
`rootWeylOperatorGroup_two_transitive_on_ovoid` theorem. It combines the
full-ovoid transitivity result with the upper-root subgroup's finite-chart
transitivity and fixed-point theorem at infinity. This is a conditional local
two-transitivity proof for that subgroup; it does not identify the external
Suzuki carrier or establish the solvability/perfectness inputs used to prove
simplicity.

The locked `SuzukiOvoid` target built successfully with 8,948 jobs after the
root-plus-Weyl inclusion, infinity-stabilizer, and two-transitivity lemmas
were added. The separate `CurtisTitsRankOne` target also built successfully
with 8,948 jobs, verifying the simple-root-torus inclusion into the adjoint
group. These builds verify only their target modules, not the full CFSG
bundle or the external family theorem.

The exact local theorem chain behind the external simplicity invocation is now
traced in `external_refs/CFSG/CFSG/ThirdParty/QiuzhenCFSG/BenderSuzuki/External/Huppert/XI/theorem_3_6.lean`.
Its private `suzukiMatrixGroup_isSimple` uses the XI.3.3 ovoid theorem to get
faithfulness, two-transitivity, the stabilizer description, and the order
formula; it proves solvability of the point stabilizer, then rules out a
nontrivial proper normal subgroup by showing its quotient is both solvable
and perfect. The local `SuzukiOvoid.lean` results currently provide point
transitivity, finite-chart transitivity for the upper-root subgroup, and a
noncommuting pair. They do not establish two-transitivity of the full local
Suzuki group, identify its point stabilizer as a solvable root-torus subgroup,
prove the corresponding solvability/perfectness inputs, or identify it with
the external `SuzukiMatrixGroup`. These are the concrete obligations for a
faithful local port of `fam_2b2_simplicity`; importing the short theorem
wrapper alone would leave its decisive mathematics unproved.

The next Suzuki port target is now narrowed to the external
`external_refs/CFSG/CFSG/LieType/Ree/SuzukiUnipotentStructure.lean` owner.
Under `Finite K` and `Nat.card K = 2 ^ (2 * a + 1)`, it proves the
two-parameter root-generator multiplication and inverse laws, identifies the
root subgroup with the parameter range, identifies its central one-parameter
subgroup, puts every commutator in that center, and concludes that the root
subgroup has derived length at most two. This is precisely the missing
solvability input for the root factor in the point stabilizer. The local
operator owner uses the transpose presentation `suzukiSGL`; a faithful port
must translate the multiplication law through that presentation and derive
the Suzuki field identities from the local automorphism hypotheses before
using the derived-series argument. The external proof itself is not imported
into the root build.

## Other external CFSG simple-family owners

The external proof surface is larger than the exceptional Lie-type table. The
current CFSG checkout has 21 Lean files under
`external_refs/CFSG/CFSG/LieType/Simplicity/`. Their direct family-level
declarations include prime-cyclic and alternating results in `Basic.lean`,
`fam_PSL_simplicity` and `fam_classical_converse` in `Classical.lean`, the
exceptional converse in `ExceptionalConverse.lean`, plus the Suzuki, Ree,
triality, and Tits family proofs listed above. The root-local catalog currently
proves the cyclic-prime and alternating model branches and PSL₂ for field size
at least four. It does not port the general classical family theorem or the
cross-family exceptional/exceptional-converse theorem.

The theorem-owner check also records the two external aggregation statements:
`fam_chevalley_exceptional_simplicity` dispatches across G₂, F₄, E₆, E₇, E₈,
²E₆, and ³D₄, while `fam_exceptional_converse` combines untwisted, Ree/Tits,
and Suzuki simplicity with finiteness. `ExceptionalCatalog.lean` and
`ModelCatalog.lean` port the corresponding local model predicates, but the
root `CFSGPort.All` API does not claim either aggregated simplicity theorem:
the underlying family-specific simplicity proofs remain the explicit debts in
the table above. This distinction matters because importing the catalog
carrier is not importing or proving its external simplicity theorem.

The current `external_refs/CFSG/CFSG/Sporadic/` source scan finds 254 Lean
files with the exact identifier `IsSimpleGroup`. This is a search count, not
a theorem-owner count: many files use simplicity as an input or intermediate
lemma. A
carrier-by-carrier source audit now reconciles all 26 local sporadic aliases
in `CFSGPort/SporadicGroups.lean` with external simplicity-owner routes. It
does not mean those proofs have been ported; the family-specific proof bodies
remain open root work.

| Local carrier | External simplicity owner route | Root status |
|---|---|---|
| M₁₁, M₁₂, M₂₂, M₂₃, M₂₄ | `Sporadic/Mathieu/M11.lean`, `M12.lean`, `M22.lean`, `M23.lean`, `M24.lean` | Carriers exist; external family proofs not ported. |
| J₁, J₂, J₃, J₄ | `Sporadic/J1.lean` plus `J1/Simple.lean`; `J2.lean` plus `J2/Simple.lean`; `J3.lean` plus `J3/Simple.lean`; `J4.lean` plus `Schreier/J4SSimple.lean` | J₁ seed operator/order lemmas are local; primitive-action certificate and simplicity proof not ported. J₂–J₄ proofs not ported. |
| Co₁, Co₂, Co₃ | `Sporadic/Co1.lean`, `Co2.lean`, `Co3.lean` | Carriers exist; external family proofs not ported. |
| Fi₂₂, Fi₂₃, Fi₂₄′ | `Sporadic/Fi22/Simple.lean`, `Fi23/Simple.lean`, `Fi24/Simple.lean` | Carriers exist; external family proofs not ported. |
| HN, HS, He, McL, O′N, Ru, Suz, Th, Ly | `Sporadic/HN.lean` (also `HNSchreier/Simple.lean`); `HS.lean`; `He.lean` (also `He/Simple.lean`); `McL/Simple.lean`; `ON.lean` (also `ON/Simple.lean`); `Ru.lean`; `Suz/Simple.lean`; `Th/Simple.lean`; `Ly.lean` and `Ly/Primitive.lean` | Carriers exist; external family proofs not ported. |
| B (Baby Monster) | `Sporadic/B.lean` | Carrier exists; external family proof not ported. |
| M (Monster) | `Milestones/FAM_M_simplicity.lean`, transported to the Griess model in `Sporadic/Bridge/MonsterModelsGriess.lean` | Carrier exists; external family proof and model transport not ported. |

This lists the 26 sporadic simple groups, with B explicitly denoting the Baby
Monster and M the Monster. The owner routes are source-navigation evidence;
the full proof dependency closures have not been imported into the root
environment. The J₁ carrier/proof gap is detailed below.

The J₁ owner illustrates a concrete carrier and proof gap. External
`CFSG.Sporadic.J1.isSimpleGroup_J` proves simplicity for the subgroup of
`GL (Fin 7) (ZMod 11)` generated by two units, using a certified primitive
action on 1,540 points and orbit/stabilizer order data. The local `J1` alias
in `CFSGPort/SporadicGroups.lean` instead names the unit group of a submonoid
closure generated from two matrices parsed from the same seed files. The
local port contains `matrixSeedEquiv` and its J₁ specialization
`j1GLSeedEquiv`. `j1Seed1_det_ne_zero` and `j1Seed2_det_ne_zero` are already
proved from explicit inverse matrices, so the local equivalence identifies
the unit-seed carrier with the subgroup generated by the corresponding
`GL` units without determinant assumptions left open. This is the local
analogue of the external `Setup.nativeEquiv` carrier step, stated on the
actual matrix operators. `J1GeneratorOrders.lean` now also proves
`j1GeneratorA_gl_matrix` and `j1GeneratorB_gl_matrix`, which show that the
transported local generators have exactly those seed matrices as their GL
operators. The external generic criterion
`isSimpleGroup_of_isPreprimitive_of_isSolvable_stabilizer` is now ported: a
perfect group with a faithful preprimitive action and solvable point
stabilizer is simple. The specialized criterion using coprime generator
orders, with its normal-subgroup and stabilizer-quotient lemmas, is also
ported as
`CFSGPort.GroupActions.isSimpleGroup_of_preprimitive_of_coprime_generator_orders`
and imported through `CFSGPort.All`. Both criteria are exposed through the
owner imported by `CFSGPort.All`. The 1,540-point primitive-action
certificate, J₁ action setup, and the stabilizer-order bound have not been
ported. The local `J1GeneratorOrders.lean` now defines the two seed
generators through the GL subgroup equivalence and proves their orders are 2
and 3 and the product order is 7; `j1GeneratorA_not_commute_B` derives that
these actual seed operators do not commute. The primitive action and stabilizer order
bound needed to apply the criterion are still missing, so the local `J1`
declaration is not yet proved simple. The `SporadicGroups` owner built
successfully through the locked Lake wrapper after this carrier-equivalence
addition. This source check was performed for J₁ only; it does not classify
the other sporadic carrier/proof pairs.

The external J₁ certificate dependency is not a standalone theorem file: its
data pipeline uses generated tables and the custom elaborator commands
`#krows`, `#ktbfs`, and `#kon_slices` in
`Certificates/Kernel/Sporadic/J1K/{Data,Checks,Final}.lean`, with the final
Boolean certificate exposed through `Certificates.Certificate3119`. A local
port must translate and kernel-check this certificate pipeline under the root
Lean/Mathlib pins; importing the external certificate namespace or treating
its generated artifacts as root proof evidence would not close the J₁ gap.

## Scope and verification

The root Lake file declares `OAI` with source directory
`external_refs/openai-math/lean`; both `InfoGeometry.lean` and
`InfoGeometry/All.lean` directly import all 21 OAI Lean files found by the
literal `IsSimpleGroup`/`isSimpleGroup` source scan. This includes the
Boone--Higman, finite-type, finite-lattice, simple-amenable, and
simple-overgroup theorem and supporting modules. `InfoGeometry.All` passed
the locked build after these imports were added (28,091 jobs, exit code 0).
The root does not declare the external CFSG tree as a Lake library. Instead,
both entrypoints import the local
`InfoGeometry.Exceptional.CFSGPort.All`, which is the root-pinned adapter
surface. This avoids treating the incompatible external CFSG checkout as if
its theorem declarations were imported into the root environment.

The current external `Blueprint/Catalog.lean` exceptional tags were compared
against the local `CFSGPort/ExceptionalCatalog.lean` constructors and model
branches. The local catalog has carrier predicates for the five untwisted
families G₂, F₄, E₆, E₇, E₈; the diagram-twisted families ²E₆ and ³D₄; the Ree
families ²G₂ and ²F₄; Suzuki ²B₂; and the Tits group. This is a source-level
family-coverage match for the external exceptional catalog. It does not mean
the external proof declarations are imported, nor that every local model has
an unconditional local `IsSimpleGroup` theorem.

A source-import-graph walk over the current local `CFSGPort/` directory finds
44 Lean owner modules, all reachable from `CFSGPort.All`; both
`lean/InfoGeometry.lean` and `lean/InfoGeometry/All.lean` import that umbrella.
This confirms module reachability only. It does not prove the declarations
compile in the current staged tree or turn conditional exceptional-family
adapters into unconditional simplicity theorems.

A source-path audit of the current Lean tree resolves all 23 distinct `OAI.*`
imports and all 8 distinct `Coxeter.*` imports to `.lean` files under the
declared in-repository Lake source directories. Because Lake resolves library
`srcDir` relative to the root package's `lean/` directory, the correct paths
are `../external_refs/openai-math/lean` and `../external_refs/lean-coxeter`.
A prior staged edit dropped the `../` prefix; a target build exposed missing
OAI files under `lean/external_refs/`. The paths have now been corrected.
Locked builds pass for `InfoGeometry.Cantor.CliffordSymmetryGroup` and
`InfoGeometry.Cantor.SimpleCantorOperatorGroup` (8,999 jobs), and for
`InfoGeometry.CoxeterPort.OperatorRepresentation` and
`InfoGeometry.Exceptional.CoxeterPort.G2CoxeterRepresentation` (9,050 jobs).
These build results verify the target closures, not every module in either
external checkout.

`ExceptionalModelSimplicity.lean` ports reusable transport steps: a
quasisimple group modulo its center is simple, equivalent model carriers
inherit simplicity, and explicit family hypotheses can be composed into a
family-level result. These adapters do not reproduce the external
family-specific proof bodies listed above. In particular, the present
conditional APIs must not be reported as unconditional simplicity proofs for
the exceptional families.

### G₂ proof dependency audit

The external `isQuasisimple_g2_of_three_le_card` proof is not a direct
normal-subgroup case split. It invokes the Tits simplicity criterion with five
structural inputs: a Curtis--Tits group datum, Steinberg extras, Bruhat extras,
root-group commutator data, and indecomposability of the Cartan matrix, in
addition to perfectness and nontriviality. The source assembles those inputs in
`CFSG/LieType/Steinberg/G2/Extras.lean` and applies the generic criterion in
`CFSG/LieType/TitsSimplicity/Simplicity.lean`.

The local port already mirrors the generic quotient arguments from
`TitsSimplicity/Simplicity.lean`: `QuasisimpleTransport.lean` proves the
perfect-group/solvable-complement lemma, simplicity of the central quotient
from the normal-subgroup dichotomy, and quasisimplicity from those inputs. The
same owner now ports the external adjoint endpoint as
`isSimpleGroup_of_quasisimple_centerless`: a quasisimple operator group is
simple once its center is proved trivial. This helper is kernel-checked; the
local G₂ centerlessness and the five family-specific Tits inputs remain open.
The external rank-one criterion is now ported in
`RankOneSimplicity.lean`: it derives centrality of a solvable Borel normal core
from the rank-one Bruhat split, a conjugation-invariant unipotent subgroup,
trivial core intersection, and normal generation. The port also includes the
subgroup-carrier transport, the perfectness criterion for a commutator
subgroup, and the reduction of an ambient Bruhat split to a subgroup. The
central-quotient simplicity and quasisimplicity theorems build through the
root `CFSGPort.All` umbrella. The criterion is generic; its hypotheses are not
yet established for a local exceptional family. Separately, the G₂
root-subgroup-to-commutator containment, perfectness, nontriviality, and
Cartan indecomposability are also present locally in `CommutatorTorus.lean`.

A source recheck found that the local port now proves reducedness for all six
untwisted exceptional root certificates and instantiates
`RootGroupCommutatorData` uniformly for G₂, F₄, D₄, E₆, E₇, and E₈. Each
root subgroup's self-commutator is trivial in the actual pinned operator
carrier, a subgroup of units of `Module.End K (RootModule τ K)`. The local
G₂ torus-commutator argument separately establishes adjoint-group
perfectness. These are operator-level results, not scalar or diagonal
substitutes.

The root-module filtration owner also proves, uniformly for the local root
tags, upper/lower triangularity of the positive/negative root-generated
subgroups, trivial intersection of those two subgroups, nilpotence with a
finite root-label bound, and solvability of the positive unipotent subgroup
(`ChevalleyRootGroupsTriangular.lean`). In finite fields it proves the
positive and negative subgroups are finite p-groups. Thus the local
`posUnipotent_isSolvable` theorem already supplies the `hU` premise of the
external generic simplicity criterion. This is a proved filtration argument
on the root-module operator group, not merely a model declaration.

The filtered commutator estimate in that owner now accepts arbitrary degrees:
if operator units lie in positive filtration levels `m` and `n`, their
commutator lies in level `m + n`. The previous first-layer bound is recovered
at `n = 1`, and the existing lower-central-series nilpotence proof still
builds against the generalized statement. The focused locked build of
`InfoGeometry.Exceptional.CFSGPort.ChevalleyRootGroupsTriangular` passed
(8,945 jobs, exit code 0) on 2026-10-30. This strengthens the local height
filtration input but does not yet give the two-root open-cone containment.

The same owner now derives
`posUnipotent_commutator_le_posFiltration_two`: the commutator subgroup of
the positive root-generated operator group lies in filtration degree two.
This is a statement on the noncommutative endomorphism-unit carrier. The
focused locked build passed again (8,945 jobs, exit code 0) after adding the
corollary. It records the first nontrivial positive-filtration layer, but the
open-cone subgroup containment remains unproved.

`CurtisTitsRankOne.lean` now supplies the local rank-one carrier as the
subgroup of endomorphism units generated by the two pinned simple-root groups.
It proves that the pinned Weyl operator and the simple-root torus lie in this
carrier, that the torus carrier lies below the rank-one subgroup, and that the
rank-one subgroup is nontrivial. This is the local operator-level `rankOne`
and part of the external `n_mem`/`H_le` data. Its torus generators now have a
kernel-checked proof that they normalize every pinned root subgroup, using
`root_torus_conjugation`; the `CurtisTitsRankOne` target built successfully
through the locked Lake wrapper. The pinned simple Weyl unit also conjugates
the positive simple-root subgroup into the negative one and conversely, with
parameter rescalings from the endomorphism identities in `ChevalleyWeyl.lean`.
The same owner now defines `simpleWeylOperatorSubgroup`, generated by all
pinned simple Weyl units on the actual root module, and exposes their action
on certified root vectors by the corresponding simple reflection with its
operator coefficient. This subgroup has not yet been identified with the
integral root-lattice Weyl subgroup or given a Coxeter presentation.
The full `IsCTGroupDatum` fields for conjugation of arbitrary root groups,
braid relations, and generation remain unassembled.
`ChevalleyBorelIntersection.lean` now defines the local operator Borel as the
join of the actual root-torus and positive-unipotent subgroups, proves it lies
in the upper filtration, and proves its intersection with the negative
unipotent subgroup is trivial. This closes the corresponding disjointness
fact for that precisely defined local subgroup. It also proves the root torus
is the supremum of its simple-root rank-one tori, matching the indexed
torus-plus-positive-unipotent shape of external `BruhatExtras`. The external
structure still requires a carrier-aligned universal root datum and the
rank-one Bruhat decomposition; those fields are still not assembled from the
local API. The local G₂ data has not yet been assembled into an instantiation
of the external generic Tits simplicity criterion, so the central-or-total
normal-subgroup conclusion and unconditional G₂ simplicity remain open. This
targeted result does not assert absence from every repository directory.

The external theorem contract is now recorded at the field level. In
`TitsSimplicity/Simplicity.lean`, `isQuasisimple` consumes a Curtis--Tits
datum (root reflection conjugation, braid relations, torus normalizers and
generation), Steinberg extras (root commutators, positive/negative root
product uniqueness, rank-one Bruhat decomposition, torus independence and
intersections), Bruhat disjointness of the Borel and negative unipotent
subgroups, root-group commutator data, Cartan indecomposability, and
perfectness. The proof derives solvability of the positive unipotent subgroup,
then proves every normal subgroup central or total using the Borel normal-core
identity. The local `RootGroupCommutatorData` now supplies the three
root-group self/doubled-root commutator clauses for all six untwisted tags,
and the local perfectness result supplies another independent input for the
untwisted adjoint groups. Neither is an instance of the
external structures: those structures quantify over the same concrete
operator root subgroups, including ordered products and conjugation laws. The
remaining implementation step is to define and prove the root-pinned G₂
Curtis--Tits, Steinberg-extra, and Bruhat-extra interfaces over
`Module.End K (RootModule .G2 K)`, including their ordered-product,
conjugation, and Borel-intersection fields.

The external `SteinbergExtras.torus_commute` field is already proved locally:
`ChevalleyRootTorusSubgroup.lean` proves pairwise commutation of every two
simple-coroot torus generators by their diagonal action on each root-module
basis vector, then proves commutativity of the generated root-torus subgroup.
This is a theorem on the noncommutative endomorphism-unit carrier, not a
replacement by a diagonal matrix group. The external
`SteinbergExtras.torus_iSupIndep` field remains distinct from torus
commutativity: it asserts independence of the rank-one subgroups. The local
operator-unit owner now proves this independence for G₂ directly and for F₄
and E₈ from integral right inverses of their Cartan matrices. The locked build
of `InfoGeometry.Exceptional.CFSGPort.CurtisTitsRankOne` passed (8,948 jobs,
exit code 0) on 2026-10-30, kernel-checking
`simpleRootTorusSubgroup_iSupIndep_G2`,
`simpleRootTorusSubgroup_iSupIndep_F4`,
`simpleRootTorusSubgroup_iSupIndep_E8`, and the shared right-inverse
argument. These results are on the noncommutative endomorphism-unit carrier.
No full `SteinbergExtras` instance is currently available.

### F₄/E₈ external criterion instantiation boundary

The external proof bodies
`Steinberg/Adjoint/Perfect.lean:isQuasisimple_f4` and `isQuasisimple_e8`
call `TitsSimplicity.isQuasisimple` with the family Curtis--Tits datum,
`SteinbergExtras`, `BruhatExtras`, root-group commutator data, Cartan
indecomposability, and the proved perfectness theorem. The local
`isSimpleGroup_adjointQuotient_of_normalDichotomy` and
`isQuasisimple_adjointGroup_of_normalDichotomy` theorems begin after the
criterion has already reduced the problem to a normal-subgroup dichotomy;
they are not ports of those external criterion applications.

On the local operator-unit carriers, F₄/E₈ perfectness, root-group
commutators, doubled-root exclusion, torus commutativity and independence,
positive/negative ordered-root-product injectivity, and Borel/negative
unipotent trivial intersection have owners in `CommutatorTorus.lean`,
`ChevalleyRootGroups.lean`, `ChevalleyRootTorusSubgroup.lean`,
`CurtisTitsRankOne.lean`, `ChevalleyProductInjectivity.lean`, and
`ChevalleyBorelIntersection.lean`. The complete local
Curtis--Tits/`SteinbergExtras`/`BruhatExtras` structures and root-pair
open-cone commutator containment are still missing. Consequently, the
external F₄/E₈ `IsQuasisimple` proofs and unconditional local family
simplicity theorems remain unported.

The root-pinned port now includes `zpow_finset_sum_local` and
`eq_one_of_prod_zpow_matrix` in `ExceptionalCartanHelpers.lean`, kernel-checked
as part of the focused 8,927-job module build. The latter is the inverse-Cartan
character step in the external adjoint-torus proof. It does not yet construct
the local character witness for arbitrary elements of the joins of the
operator rank-one tori, so it is not itself an `iSupIndep` result.
`CurtisTitsRankOne.lean` now also proves
`torusElt_eq_one_of_torusElt_G2_eq`: equality of the two G₂ simple-coroot torus
operators forces both field-unit parameters to be one, by evaluating on the
two simple-root basis vectors and combining the resulting Cartan-weight
equations. The source now also contains
`simpleRootTorusSubgroup_iSupIndep_G2`, which reduces the subgroup-level claim
to the two-index independence criterion and the trivial intersection of the
generated operator tori. The focused locked build of
`InfoGeometry.Exceptional.CFSGPort.CurtisTitsRankOne` passed (8,947 jobs), and
the `InfoGeometry.Exceptional.CFSGPort.All` umbrella passed (8,967 jobs) on
2026-10-29. The G₂ subgroup-independence theorem is therefore kernel-checked.

The ordered-product fields have a more substantial translation boundary than
the triangular filtration alone suggests. External
`CFSG.LieType.Steinberg.Adjoint.Group.prodInjective` first represents each
root-group element by its pinned parameter, then invokes
`RootOperatorFamily'.prod_eltOr_injective`; that argument isolates each
parameter from the first nonzero height layer of the operator product. The
local tree has no `RootOperatorFamily` or `eltOr` owner (confirmed by a source
search), but it does provide the corresponding endomorphism-unit `pinnedX`
polynomial, `pinnedX_weight_shift`, and the finite height filtration. The
local parameter-isolation proof now yields positive and negative
`rootSubgroup_prodInjectiveFor` theorems on the operator-unit carrier, as
recorded below. This is an API-level port of the external product-uniqueness
fields; it does not construct the surrounding `SteinbergExtras` record. No
scalar, diagonal, or commutative carrier is used.

A repository-wide search for `commContained`, `openCone`, root-group products,
and root/weight commutators found no existing theorem on the local root-module
unit groups that supplies this independent-root commutator containment. The
nearby matches are positive-filtration bounds for commutators of positive
operators and multigraded Lie-algebra commutator laws; neither identifies the
commutator with the subgroup generated by roots in the two-root open cone.
`ChevalleyStrings.lean` supplies kernel-checked integer root-string intervals,
but the local API still needs the corresponding coefficient-level operator
commutator/factorization argument. This is the next proof boundary after the
now-verified positive and negative ordered-product uniqueness theorems.

The external implementation of that field is now traced to
`CFSG/LieType/Chevalley/RootOps/Comm.lean`, `Poly.lean`, `Cover.lean`, and
`CommAll.lean`. The simple-root case is derived from per-tag lists of root
factorizations and Boolean `repCheck`/`coverCheck` certificates: the factor
checks verify the operator product identity, and the coverage check transports
each positive-height root pair to one of those checked representatives by a
finite simple-reflection word. `commContained_pos` then uses positive
definiteness of the symmetrized Cartan matrix to find a reflection lowering
positive root height, and inducts from a simple root. This gives a concrete
port target: translate the checked operator factorization/coverage data to
local pinned operators, then port the reflection-height induction. The local
root and string certificates establish root combinatorics, but are not those
operator factorization certificates.

`ChevalleyProductInjectivity.lean` proves the positive and negative
ordered-product uniqueness fields on the local endomorphism-unit root groups.
Its reusable `RaisesBy` filtration lemmas show that pinned-root operators
raise additive root gradings, isolate the coefficient of a specified lattice
shift, and force equality of all parameters in a nodup ordered root product.
The resulting `rootSubgroup_prodInjectiveFor` and negative-grade counterpart
are height-specialized to match the external `SteinbergExtras` conditions.
The focused locked build passed (8,947 jobs, exit code 0), and the public
`CFSGPort.All` umbrella rebuilt with the owner in its import closure (8,968
jobs, exit code 0) on 2026-10-29. These are verified local ports of both
product-injectivity fields; they do not construct the surrounding
`SteinbergExtras`/`BruhatExtras` records or prove an exceptional family simple.

`CurtisTitsRankOne.simpleRootTorusSubgroups_commute` now proves the local
`SteinbergExtras.torus_commute` field for any two simple-root torus elements:
each lies in the commutative subgroup generated by the actual torus
endomorphism units. The focused locked target
`InfoGeometry.Exceptional.CFSGPort.CurtisTitsRankOne` passed (8,947 jobs, exit
code 0). Alongside the existing all-tag root-subgroup nontriviality,
double-root containment, positive/negative unipotent intersection, normalizer,
and torus/positive-unipotent intersection theorems, this leaves the
root-commutator/open-cone field, the rank-one Bruhat decomposition, and
simple-root torus independence for E₆ and E₇ as central gaps in a
full local `SteinbergExtras` record.
The public umbrella `InfoGeometry.Exceptional.CFSGPort.All` rebuilt
successfully with this commutation theorem in its import closure (8,968 jobs,
exit code 0) on 2026-10-29.

`ChevalleyBorelIntersection.simpleRootTori_inf_posUnipotent` now proves the
local `SteinbergExtras.torus_inf_posPart` field on the endomorphism-unit root
module. It rewrites the supremum of the actual simple-root operator tori to
the generated root torus and applies the checked diagonal-versus-positive
unipotent intersection theorem. The focused locked target
`InfoGeometry.Exceptional.CFSGPort.ChevalleyBorelIntersection` passed (8,950
jobs, exit code 0) on 2026-10-30. The remaining major interface gaps include
the root-commutator/open-cone field, rank-one Bruhat, and torus independence
for E₆/E₇; this field alone does not establish an exceptional simplicity
theorem.

### Root-pair commutator port boundary

A repo-wide Lean-source search on 2026-10-30 found no local declarations named
`RingCommContained`, `commContained_pos`, `commutatorFormula_commC`, or
`commutator_mem_openCone_of_linIndepPair`. The local CFSG port does have
checked Chevalley string certificates (`ChevStrSound.lean` and
`ChevalleyStrings.lean`), pinned-root parameter injectivity and abelianity
(`ChevalleyRootGroups.lean`), and the general filtered-operator commutator
bound (`ChevalleyRootGroupsTriangular.lean`). These establish root strings
and height filtration, but not the two-root subgroup containment required by
`SteinbergExtras.commutator_mem`.

The external theorem's actual dependency chain is
`Chevalley/RootOps/RingComm.lean:ringCommContained_pos` →
`Chevalley/RootOps/CommAll.lean:commContained_pos` →
`Steinberg/Adjoint/CommAll.lean:commutator_mem_openCone_of_linIndepPair`;
family presentation records then supply the commutator formula through
`Steinberg/Adjoint/ChevExtras.lean:commutatorFormula_commC` and
`Steinberg/Adjoint/Presentation.lean`. The local port should start by
formalizing the ring-level root-operator commutator containment on its actual
endomorphism-unit carrier, using the already checked string data. Importing
the external module directly would bypass the root pin and is not a valid
substitute for this port.

The torus-independence coverage has advanced: the existing rank-two G₂ proof
and new Cartan-right-inverse ports establish the field for G₂, F₄, and E₈ on
the operator tori. The F₄ and E₈ instances use checked integral inverses of
their Cartan matrices. The generic theorem is conditional on such an inverse;
the local E₆ and E₇ Cartan matrices have no integral right inverse, so this
argument does not cover those types.
With the F₄/E₈ independence theorems in place, the public umbrella
`InfoGeometry.Exceptional.CFSGPort.All` rebuilt successfully (8,968 jobs,
exit code 0) on 2026-10-29.

After the positive/negative height adapters were added, the full repository
target `InfoGeometry.All` passed with 28,136 jobs and exit code 0 on
2026-10-29. Its audit found zero declarations natively depending on
`sorryAx`; it also reports 303 generated explicit axiom constants from
`native_decide` expansions elsewhere in the repository, so this is not a
claim that the whole codebase is axiom-free.

The local source adapters and the Clifford random-average generator action
have been checked with the locked Lake build in the root Lean 4.34.1
environment. No root toolchain or Mathlib pin was changed. Ordinary builds
used the existing cache; no cache-cleaning command was run.

The root Mathlib manifest remains pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`). The `lean-coxeter`
submodule manifest pins the same revision and its toolchain is `v4.34.1`.
The source-path correction changes only Lake source locations; it does not
change dependency revisions or cache contents.

The earlier `InfoGeometry.All` failure recorded above was superseded by a
successful locked build of the current tree on 2026-10-29: all 28,136 jobs
completed with exit code 0, including `InfoGeometry.Audit` and
`InfoGeometry.AllExhaustive`. The audit reported zero declarations depending
on `sorryAx` and 303 generated explicit `native_decide` axiom constants in
other owners. This build verifies the current aggregate; it does not certify
the full repository as axiom-free.

## External exceptional simplicity theorem to local port map

The external source below states the indicated family theorem. “Conditional
local adapter” means the local theorem transports simplicity after receiving
the listed family result or structural hypotheses; it is not a derivation of
the external theorem from the local model.

| Family | External theorem owner | Current local model / status |
|---|---|---|
| G₂, F₄, E₆, E₇, E₈ | `CFSG/LieType/Simplicity/Exceptional.lean`: `fam_g2_simplicity`, `fam_f4_simplicity`, `fam_e6_simplicity`, `fam_e7_simplicity`, `fam_e8_simplicity` | Local Chevalley models and noncommutative root-module operator groups are imported. `ExceptionalModelSimplicity.lean` supplies conditional model transport; G₂ has additional local operator inputs, but no family theorem closes the remaining quasisimplicity/normal-subgroup proof. E₆/E₇ also lack the current integral-Cartan torus-independence route. |
| ²E₆ | `Exceptional.lean`: `fam_2e6_simplicity` | Twisted fixed-derived model and conditional simplicity transport are present. The external family-specific quasisimplicity proof is not ported. |
| ³D₄ | `CFSG/LieType/Simplicity/TrialityD4.lean`: `fam_3d4_simplicity` | Triality fixed-derived model and conditional transport are present; external quasisimplicity remains open locally. |
| ²G₂ | `CFSG/LieType/Simplicity/ReeSmall.lean`: `fam_2g2_simplicity` | Ree relation model and conditional transport are present; family arithmetic inputs exist, but the full external quasisimplicity proof is not ported. |
| ²F₄ | `CFSG/LieType/Simplicity/ReeLargeModel.lean`: `fam_2f4_simplicity` | Ree relation model and conditional transport are present; the family-specific local quasisimplicity proof remains open. |
| Tits group | `CFSG/LieType/Simplicity/TitsModel.lean`: `fam_tits_simplicity` | Tits relation model and conditional transport are present; external fixed-group quasisimplicity is not yet a local proof. |
| ²B₂ (Suzuki) | `CFSG/LieType/Simplicity/Suzuki.lean`: `fam_2b2_simplicity` | Local four-dimensional general-linear operator group, projective ovoid, generator-preservation lemmas, and a noncommuting pair are present. The external theorem requires `SuzukiModel`; local model identification plus its simplicity proof are not established. |

This map covers the exceptional Lie-type theorem owners listed in the
external-source section, not every simplicity theorem anywhere in the large
CFSG checkout. The source-level inventory in
`docs/SYMMETRY_GROUP_INVENTORY.md` is likewise a broad navigation/classification
artifact; it does not claim a completed semantic audit of every group-like
declaration in every repository language.

## External sources

- `external_refs/CFSG/CFSG/LieType/Simplicity/Exceptional.lean`
- `external_refs/CFSG/CFSG/LieType/Simplicity/TrialityD4.lean`
- `external_refs/CFSG/CFSG/LieType/Simplicity/ReeSmall.lean`
- `external_refs/CFSG/CFSG/LieType/Simplicity/ReeLargeModel.lean`
- `external_refs/CFSG/CFSG/LieType/Simplicity/TitsModel.lean`
- `external_refs/CFSG/CFSG/LieType/Simplicity/Suzuki.lean`

## Local API source

- `lean/InfoGeometry/Exceptional/CFSGPort/ExceptionalModelSimplicity.lean`
- `lean/InfoGeometry/Exceptional/CFSGPort/QuasisimpleTransport.lean`
- `lean/InfoGeometry/Exceptional/CFSGPort/ExceptionalCatalog.lean`
- `lean/InfoGeometry/Exceptional/CFSGPort/SporadicGroups.lean`

## G₂ Tits-criterion dependency audit (2026-10-30)

The external `CFSG/LieType/Steinberg/G2/Perfect.lean` proves
`isQuasisimple_g2_of_three_le_card` by assembling `g2_isCTGroupDatum`,
`g2_steinbergExtras`, `g2_bruhatExtras`,
`g2_rootGroupCommutators`, Cartan indecomposability, and the local
perfectness theorem. This separates two similarly named commutator
obligations:

- The Tits-criterion input `RootGroupCommutators` is already covered on the
  local endomorphism-unit carrier by
  `CommutatorTorus.rootGroupCommutatorData_all`. Its same-root commutator is
  trivial because each pinned root subgroup is abelian, and the doubled-root
  cases are impossible by the checked reduced-root certificates. It is a
  local API equivalent in content, not an import of the external structure.
- The still-open field is `SteinbergExtras.commutator_mem`: for independent
  roots, the commutator must lie in the subgroup generated by roots in their
  open cone. The external proof derives this from root-operator
  `CommContained`, height movement under the Weyl group, and cone inclusion.
  The local positive-unipotent filtration bound only proves that commutators
  raise filtration degree; it does not identify the required open-cone root
  subgroup.

The external derivation is implemented across
`CFSG/LieType/Chevalley/RootOps/Comm.lean`, `CommAll.lean`, `Cover.lean`, and
`Poly.lean`: polynomial root-operator checks prove containment for a simple
root and another positive root, a finite induction extends it to all positive
root pairs, and Weyl transport reduces independent roots to the positive
case. The local port has checked root-string data in `ChevalleyStrings.lean`
and operator product injectivity in `ChevalleyProductInjectivity.lean`, but a
repo-owned search of `lean/InfoGeometry/Exceptional/CFSGPort` found no
`CommContained` or root-operator commutator identity corresponding to those
external owners. The port needs the polynomial commutator identity and its
root-cone product factorization before `SteinbergExtras.commutator_mem` can be
assembled; the existing filtration-degree theorem is insufficient.

A source-level comparison of the external certificate path with the local
port narrows the prerequisite further. `ChevalleySparsePolynomial.lean`
already proves the sparse bivariate operator multiplication and evaluation
laws, while `ChevalleyRootOperatorTables.lean` imports the six local root-code
tables. The local tree does not yet define the external `Factor`, `repsCheck`,
`coverCheck`, or `RootOperatorFamily` interfaces, nor prove that a sparse root
operator from those tables equals the pinned root operator used by
`adjointGroup`. Therefore the external `g2Reps`/`g2Cover` (and corresponding
F₄, D₄, E₆, E₇, E₈ tables) cannot yet be promoted as local commutator proofs.
The next concrete port layer is that carrier-and-operator bridge, followed by
local certificate checks and the open-cone factorization theorem.

The remaining G₂ assembly also requires local counterparts of the full
Curtis–Tits datum and Bruhat extras at the `adjointGroup .G2 K` carrier. The
local rank-one Weyl and torus lemmas, Borel solvability, normalizer facts, and
perfectness theorem are ingredients, but do not currently package those full
interfaces. Consequently this audit does not promote G₂ quasisimplicity or
exceptional-family simplicity to a local theorem.

The external `SteinbergExtras` fields were cross-checked against the local
owners rather than treating the whole structure as one missing block:

| External field | Local operator-carrier evidence | Status for assembly |
|---|---|---|
| `ne_bot` | `ChevalleyRootGroups.rootSubgroup_ne_bot` | Present over nontrivial fields. |
| `two_smul_le` | `CommutatorTorus.rootSubgroup_two_smul_le` | Present; reduced-root certificates rule out its doubled-root premise. |
| `commutator_mem` | External `RootOps/CommAll.lean` and `RootOps/Poly.lean` | Open; local root-string checks do not yet prove operator commutator factorization into the open cone. |
| `prodInjective_pos`, `prodInjective_neg` | `ChevalleyProductInjectivity.rootSubgroup_prodInjective_height_pos` and `_neg` | Present as height-ordered product injectivity for the local root groups. |
| `posPart_inf_negPart` | `ChevalleyBorelIntersection.adjointGroup_posUnipotent_inf_negUnipotent` | Present after restricting to the adjoint operator group. |
| `rankOne_bruhat` | `CurtisTitsRankOneBruhat` proves two-cell coverage, exports the external factor order as `operatorRankOne_bruhat`, and transports it into the adjoint carrier as `adjointGroup_rankOne_bruhat` | Local field-shaped theorem proved; the complete external-style structure remains to be assembled with its other fields. |
| `eq_one_of_mem_normalizer` | `ChevalleyNormalizerTriviality.adjointGroup_eq_one_of_mem_normalizer_negSimpleRoot` | Present on the local adjoint carrier. |
| `torus_commute`, `torus_iSupIndep` | `CurtisTitsRankOne.simpleRootTorusSubgroups_commute` and `_iSupIndep_G2` | Present for the two G₂ simple-root tori. |
| `torus_inf_posPart` | `ChevalleyBorelIntersection.simpleRootTori_inf_posUnipotent` | Present on the full endomorphism-unit carrier; its local statement identifies the simple-root torus join with the root torus. |

After the rank-one port, the substantive missing G₂ `SteinbergExtras` input
in this map is `commutator_mem`; complete interface assembly still remains.
The local G₂ perfectness proof uses the Weyl/torus commutator action and does
not discharge the open-cone commutator field.
`ChevalleyRootBasis.lean` now proves that certificate indices enumerate the
actual root-module basis, with injectivity, surjectivity, and an operator
extensionality theorem. `ChevalleySparseOperators.lean` interprets sparse
integer entries as endomorphisms and proves their ordered composition law.
`ChevalleyOperatorPolynomial.lean` proves ordered polynomial multiplication,
coefficient collection, and evaluation equality from coefficient equality.
The focused build passed (8,930 jobs); the public CFSG umbrella passed
(8,972 jobs). Axiom audits of the six principal theorems report only
`propext`, `Classical.choice`, and `Quot.sound`. These are soundness foundations;
the root-specific sparse coefficient tables, their agreement with the pinned
root operators, and the open-cone commutator factorizations remain to be ported.

`ChevalleySparseColumns.lean` now ports sparse-vector evaluation, column
extraction, and the theorem that column agreement is equivalent to equality
with a given root-module endomorphism. `ChevalleySparseCertificate.lean`
ports the external bounded encoding checker and proves
`entriesOp_eq_of_summaryEq`: a successful check implies equality of the
actual operators over every commutative coefficient ring. The checker
requires both indices below 256 and each absolute coefficient sum below
512; these bounds are part of its soundness proof. The focused certificate
build passes (8,931 jobs), and the public CFSG umbrella passes (8,974 jobs).
These general checker theorems do not yet instantiate the root-specific
commutator certificate tables.

`ChevalleySparsePolynomial.lean` now ports the external bivariate sparse
format, its ordered multiplication and validity-preservation laws, and
`pOp_eq_of_pEqCheck`: coefficient checks imply operator equality for all
parameter pairs over a commutative coefficient ring. `pOp_eq_eval` identifies
this sparse evaluator with the native operator-coefficient evaluator. The
public CFSG umbrella passes with 8,975 jobs. Root-specific table agreement
with the pinned generators remains the next missing connection.

`ChevalleyRootTableAction.lean` now derives reflection-table correctness and
the computable downward-string sign from the existing root/string
certificates. `ChevalleySparseWeyl.lean` proves that the resulting sparse
basis-column action and sparse-vector action agree with the pinned
`weylElt` endomorphism, uniformly for all six local tags. This connects the
Weyl-action part of the sparse format to the actual operator representation.
The public CFSG umbrella passes with 8,977 jobs. Root-generator coefficient
tables and the commutator factorizations still remain.

The six `RootOps/Data/{G2,F4,D4,E6,E7,E8}.lean` coefficient/sign/image tables
are now ported under `CFSGPort/RootOperatorData/`; a source comparison confirms
that only the namespace and attribution header changed.
`ChevalleySparseNormalize.lean` proves normalization preserves the represented
root-module vector. `ChevalleyRootOperatorTables.lean` supplies decoding and
validity predicates; `ChevalleyRootOperatorValidity.lean` proves `allValid_tag`
by kernel reduction for every tag and exports `entries_valid` for every root
index and degree 1–3. The public CFSG umbrella passes with 8,986 jobs.
The tables are therefore imported and index-valid. For G₂, `conjRange_G2`
now kernel-checks the full root-by-simple-reflection table for degrees 1–3.
`conj_of_conjCheck` turns each checked row into an operator conjugation identity
on the actual root-module endomorphisms. This does not yet identify the entry
tables with the pinned root generators, and the corresponding conjugation ranges
for F₄, D₄, E₆, E₇, and E₈ plus all commutator factorizations remain open.

The outer G₂ family adapter is not itself the missing port. External
`CFSG/LieType/Simplicity/Exceptional.lean: fam_g2_simplicity` unpacks the
exceptional model, obtains the field-cardinality lower bound, applies
`Steinberg/Adjoint/Perfect.lean: isQuasisimple_g2_of_three_le_card`, and
transports simplicity across the model equivalence. Local
`ExceptionalModelSimplicity.isSimpleGroup_of_G2Model` and
`g2_family_simple_of_adjoint_quasisimple` already express that model
transport. The missing theorem-bearing step is the unconditional local
fieldwise statement
`IsQuasisimple (↥(Chevalley.adjointGroup .G2 K))` for finite fields with
`3 ≤ Nat.card K`; the existing local conditional normal-dichotomy adapters
and perfectness theorem do not prove it.


### Compressed Weyl table and sparse conjugation port

`ChevalleyFastWeylTables.lean` is now exported by `CFSGPort.All` and its
focused build has passed. It imports the six exceptional compressed image
tables, kernel-checks `tabCheck` for G2/F4/D4/E6/E7/E8, and proves that the
decoded rows compute the pinned Weyl endomorphism on every basis vector.
The port also defines `nColF` and `conjEntries`; proves the row/column case
lemmas, coordinate-functional list expansion, the single-row operator
expansion, and `entriesOp_conj_single`; and establishes validity of each fast
row. The latest focused build result is recorded in
`/tmp/fast-nrow-build.log` (success, 8953 jobs); the umbrella build including
this module previously passed with 8987 jobs.

The basis-coordinate identity `coordOf_nColF_weylElt_posVec`, its linear-map
extensionality consequence `coordOf_nColF_comp`, and the full
`entriesOp_conjEntries_mul` theorem are now ported and kernel-checked. The
owner build passed, and the updated `CFSGPort.All` umbrella rebuild passed
(8987 jobs, `/tmp/cfsg-fast-all.log`). This closes the sparse Weyl conjugation
layer for the imported exceptional tables. It does not validate any
exceptional commutator table, assemble the remaining G₂/other family
quasisimplicity inputs, prove exceptional simplicity, or complete the
repository-wide symmetry census. The local Lean 4.34.1 and Mathlib pins remain
unchanged.


### Root-operator conjugation checker soundness

`ChevalleyFastChecks.lean` now ports the external column-check implication,
including support control for sparse columns. `conj_of_conjCheckAux` proves the
full operator identity from a successful finite checker, and
`conj_of_conjCheck` specializes it to the imported root-operator tables. The
local `conjRange_G2` proof checks every root index, every simple reflection,
and degrees 1–3 with kernel reduction (`decide +kernel`). The focused locked
build passed (8,954 jobs), and the public `CFSGPort.All` umbrella passed
(8,988 jobs). This verifies G₂'s table conjugation equations on
the sparse operators represented by the tables. Identification of those
sparse operators with the pinned root-generator exponentials and the analogous
five other tag ranges remain unproved. The theorem is exported through
`CFSGPort.All`; no dependency pin or external submodule source was changed.
The root `InfoGeometry.All` umbrella also rebuilt successfully (28,236 jobs),
confirming integration with the current root import closure. Its audit reports
zero declarations depending on `sorryAx` and 303 generated explicit axiom
constants elsewhere in the repository; this is not an axiom-clean repository
claim.

The newest root-pinned verification is after importing
`ChevalleyRootHeightDescent`: `InfoGeometry.Exceptional.CFSGPort.All` passed
with 8,990 jobs and `InfoGeometry.All` passed with 28,248 jobs on
2026-10-30. The audit again reported zero declarations depending on `sorryAx`
and 303 generated explicit `native_decide` axiom constants elsewhere in the
repository. The root dependency pins remain unchanged.

### Positive-root height descent port (2026-10-30)

`ChevalleyRootHeightDescent.lean` now proves
`exists_reflect_height_lt` for the six exceptional root systems in the local
catalog. It transports each inductively generated root through the checked
finite root certificate, where kernel reduction verifies a simple reflection
that preserves positive height and strictly lowers it. This ports the
height-induction step used by the external
`CFSG.LieType.Chevalley.RootOps.CommAll.commContained_pos` proof. The focused
locked build passed (8,942 jobs), followed by the public
`InfoGeometry.Exceptional.CFSGPort.All` build (8,990 jobs). The root Lean
4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` pins are
unchanged. `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound` for the exported theorem.

This does not prove the root-operator commutator containment statement. The
remaining step is to identify the external sparse commutator tables with the
local pinned root operators, then prove factorization into the open-cone root
subgroup. Consequently the Tits simplicity criterion and unconditional
exceptional family simplicity remain open.
