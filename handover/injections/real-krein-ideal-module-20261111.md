# Real doubled ideal modules: theorem contract

## Intake and provenance

- Task: turn the attached generated mathematical stream into canonical Lean 4 / Mathlib theorems.
- Intake: `Pasted text(20261111-134359).txt`, supplied in this conversation on 2026-11-11.
- SHA-256: `89a73eeaf422b2e9b16c5deb69587b8487d633e184860fa1eb2b7d241ccac00f`.
- The source attachment is preserved separately; its rhetoric is not proof evidence.
- Base: `c143c264bc18bbf41d692be4e270b5b7f7405702`.
- Branch: `feat/real-krein-ideal-module`.
- Pins: Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Carriers, operations, and actual dependencies

The generic coefficient carrier is a possibly noncommutative unital ring `B`.
Star results add `[StarRing B]`; positivity is not inferred from this class.
The doubled column carrier is `Fin 2 → B`, canonically equivalent to `B × B`.
Its operators are native `Matrix (Fin 2) (Fin 2) B`, already named `BdGBlock B`.
Matrix entries act from the left. This action is real-linear for real algebras
and right-`B`-linear, not generally left-`B`-linear.

The ideal carrier is the existing native `idempotentLeftIdeal p hp : Submodule B B`.
The corner is Mathlib's `IsIdempotentElem.Corner`; its existing opposite-ring
equivalence with `Module.End B (idempotentLeftIdeal p hp)` must be reused.
No alternate ideal or corner carrier is to be introduced.

The concrete infinite coefficient ring is exactly
`Cl11TensorTowerLimit.Limit`, the existing algebraic direct limit of full real
matrix stages under `A ↦ A ⊗ I₂`. Its star is the stagewise transpose star.
The faithful stage maps and star-algebra universal property are already proved
in `Cl11StarAlgebraColimit`. `Cl11StarAlgebraFiltration` supplies a strict native
subalgebra chain, common finite stages, and algebraic infinite dimensionality.
No identification with `SplitCliffordInfinity`, Clifford reversion, or a Hilbert
completion is assumed.

## Existing owners read and reused

| Claim | Existing owner / declarations |
|---|---|
| Native ideal and opposite corner | `OperatorAlgebra.PeirceSpine.TripotentCornerEndEquivalence`: `idempotentLeftIdeal`, `idempotentCornerEndEquiv` |
| Scalar-linear commutant | `Algebra.IdempotentCornerCommutant`: `leftIdealCommutant_eq_rightCornerRange`, `rightCornerAction_cornerMul` |
| Ordered sandwich composition | `Core.PeirceBilateralAction`: `bilateral_comp`, `bilateral_mul_defect` |
| Idempotence obstruction | `Core.IdempotencyDefect.defect` |
| Native doubled matrices | `Physics.BdGChiralBlockMatrix`: `BdGBlock`, `chiralGrading`, `andreevSwap`, full square with commutators |
| Actual doubled endomorphisms | `OperatorAlgebra.LieJordanCliffordDouble`: `swapOp`, `gradingOp`, `phaseOp` |
| Ring-valued column pairing | `CliffordWeyl.SpinorBilinearSoldering`: `diracRow`, `bilinear` |
| Noncommutative metric adjunction | `CliffordWeyl.DiracSolderOperatorAction.bilinear_metric_adjoint_action` |
| Twisted star | `Canonical.SpinorialCore.KreinAdjoint`: `sharp`, `sharp_mul`, `sharp_involutive` |
| Involution projectors | `Algebra.CyclotomicOperatorProjectors`: the noncommutative `_of_commute` projector lemmas |
| Faithful positive colimit trace | `Canonical.TensorExactCurvatureTrace`: `normalizedTraceLimit_star_mul_self_nonneg`, `normalizedTraceLimit_star_mul_self_eq_zero_iff` |

The general ring/star sections are reused without importing their later
commutative specializations as hypotheses for operator claims.

## Atomic targets and dependency order

1. **Support / duality.** For `p*p=p`, right multiplication by `a` preserves
   `Bp` iff `p*a*p=p*a`, equivalently `p*a*(1-p)=0`. The induced endomorphism
   equals the existing right action of the corner representative `p*a*p`.
   Star exchanges `x*p=x` with `star p * star x = star x` without assuming
   `star p=p`.
2. **Rectangular pairing.** If `φ*p=φ` and `ψ*p=ψ`, then
   `star p * (star φ * ψ) * p = star φ * ψ`.
   Whole-ideal isotropy is equivalent to the vanishing of all sandwiches
   `star p * a * p`, not the single product `star p*p`.
3. **Ordered Gram / density mechanics.** For `N=star ψ*ψ` and `ρ=ψ*star ψ`,
   prove `ρ^(n+1)=ψ*N^n*star ψ`,
   `defect ρ=ψ*(N-p)*star ψ` under `ψ*p=ψ`, the sufficient normalization
   implication, and right-unitary density invariance. No bijection between
   generators and densities is asserted.
4. **Doubled metric.** For a self-adjoint involution `η`, construct the native
   matrix `G=diag(η,-η)`. Prove `G*=G`, `G²=1`, the real matrix generator
   identities, and cancellation of the column pairing
   `bilinear G G v w = star v ⬝ᵥ w`.
   Distinguish this from the operator sharp `G*star X*G`: the extra left
   factor `G` in operator-ideal products must not be silently dropped.
5. **Actual-colimit definiteness.** Reuse the established faithful trace to
   prove the two-square zero criterion in `Limit`, then strict definiteness
   of the doubled column Gram and `star X*X=0 ↔ X=0` for `BdGBlock Limit`.
   This proves algebraic definiteness for the chosen star; it does not equip
   an arbitrary `StarRing` with an order or establish a Hilbert completion.
6. **Noncommutative Dirac defect.** For
   `D = !![m,b; -star b,-m]`, retain both ordered diagonal products and both
   off-diagonal commutators in `D²`. Give the exact square-zero criterion.
   If an invertible gap commutes with `D` and `D²=V²`, normalize to an
   involution and reuse the existing projector lemmas. The hypotheses are
   parameters, not an inferred mass-domination theorem.
7. **Countermodels.** Prove finite exact real-matrix witnesses for the false
   isotropy and exceptional-horizon implications. Their scope is finite
   counterexample evidence; they do not replace generic operator theorems.

These dependencies form a DAG: support precedes rectangular pairing and
density identities; metric cancellation and actual-colimit trace faithfulness
jointly precede doubled definiteness; the full Dirac square and the explicit
gap hypotheses precede the normalized involution and projector conclusions.
There is no causal edge from an archetypal label or from graph placement alone.

## Rejected or unproved interpretations

| Intake claim | Disposition |
|---|---|
| `star p*p=0` makes the entire ideal isotropic | False; prove countermodel and exact sandwich criterion. |
| Right multiplication preserves `Bp` only for `a∈pBp` | False; the exact criterion is `pap=pa`, with `1` an immediate exception to the stronger claim. |
| `star p≠p` forces zero norm | False; non-self-adjoint idempotents can have nonzero positive Gram. |
| Star duality forces a unique doubling | Not a deduction; the doubled carrier is explicitly constructed. |
| `Bp ⊕ Bq` is preserved by every `Mat₂(B)` | False in general; distinct ideals require cross-block support conditions. `Mat₂(B)diag(p,q)` is a matrix ideal with four entries. |
| Every corner element is a gauge automorphism | False; invertible or unitary corner elements require the corresponding hypotheses. |
| Cancelling the metric proves positivity in every star ring | False; positivity is specialized to the established faithful real-matrix colimit. |
| Full real matrix rings are formally real in the ordinary sum-of-squares sense | False (`J²=-1`); use proper transpose star and positive trace terminology. |
| Diagonal horizon equalities imply `D²=0` | False without the off-diagonal commutator conditions. |
| A central invertible gap alone supplies a positive dynamical metric | False; even a negative scalar mass gives the opposite metric orientation. |
| Physical CPT theorem, particles, ghosts, Jordan-ideal classification, Morita equivalence | Open interpretation/classification debt; no theorem with these stronger names is promoted. |

## Authoring and acceptance

- Generation: parent plus isolated candidate proposals from the ideal and
  operator workers. Parent reviews and integrates into canonical owners.
- Semantic audit: independent `math_audit`, read-only.
- Acceptance: independent `acceptance_qa`, read-only source/artifact review.
- Required evidence: exact pinned compilation of the changed owners and
  repository import closure; strict proof screening; native declaration and
  axiom audit permitting only `propext`, `Classical.choice`, `Quot.sound`;
  no new-owner warnings; staged hook; root-package gate attempted and scoped.
- All local compilation, tests, and cache operations use the maintained
  shared build lock. No dependency updates, cache deletion, or lock bypass.
- Final report records source/artifact hashes, exact commands, CI revision,
  independent findings, and any repository-level blocker separately.

Status: contract frozen before theorem-bearing edits; implementation and
acceptance pending.
