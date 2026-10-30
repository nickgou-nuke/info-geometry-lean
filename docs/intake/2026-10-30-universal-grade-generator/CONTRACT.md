# Universal grade-generator intake: mathematical contract

Status: generation contract, written before theorem authoring.

## Frozen source and scope

The intake is `AGENTS-Universal-Grade-Generator.md` at repository commit
`f54b83da3756c3ded0decbf92fd887f8083949ed`, blob
`1817347ef5f50f799912ba3bd7d03dc40c842bdc` (654 lines). That immutable file
preserves the complete source, including the narrative and unsupported claims.
Its title is an intake label, not an instruction to execute its embedded macros.

The mathematical target is finite algebra on an arbitrary associative ring,
and real linear operator algebra where scalar division or eigenspaces require
it. The concrete instance is the full algebra `Matrix (Fin 4) (Fin 4) ℝ`.
No assumption makes the ambient algebra commutative. Orthogonal projectors
commute with each other, as they must, while the operators between their
ranges need not commute with the generator or with each other.

This is risk R2 (new consequences of existing owners) plus an R1 explicit
matrix instance. It does not construct a colimit, completion, manifold,
compact Lie group, or physical model. The categorical infrastructure map was
read; its owners remain authoritative for any later colimit transport.

## Owner-grounded inventory

| Source atom | Carrier and hypotheses | Existing proof-bearing owners | Smallest new work |
|---|---|---|---|
| A55 polarization and sign separation | `[Ring A]`; `δ x = x*x-x` | `Core/PeirceQuadraticFrame`, `Core/LieJordanGenerators` own related frame identities, but the searched general defect API is absent | A small reusable defect calculus, homomorphism naturality, polarization, sign and product formulas |
| A55 tangent shift | `p*p=p`; `p*y+y*p=y` in the full ring | `Core/PeirceDecomposition`, `Core/IdempotentCartan`, `Core/PeirceGrading` | `δ(p+y)=y*y` iff the tangent equation; mixed-corner characterization; the square commutes with `p` |
| A55 opposite corners and operator correction | `u ∈ peirce10 p`, `v ∈ peirce01 p` | `Core/PeirceCoupledCorners`, `Core/PeirceQuadraticFrame`, `Core/PeirceAdjointCycle` | Defects of `p+u`, `p+v`, `p+u+v`, `p+u-v`; native adjoint-square correction retaining `K*K-K`, where `K=u*v+v*u` |
| A55 finite defect iteration | Native `Function.iterate`; any associative algebra | Native subalgebra and commutation APIs in pinned Mathlib | Preservation of commutation and mutually annihilating sums; the generated subalgebras form an antitone chain in the native `Subalgebra` order |
| A56 off-shell tripotent formulas | `τ t=t*t*t-t`, no tripotence assumed | `Physics/Algebra/TripotentPeirceProjectors` owns `projPos`, `projNeg`, `projZero` | Exact polynomial defect formulas, including the corrected positive zero-projector defect |
| A56 idempotent adjoint | `p*p=p`; native `LieAlgebra.ad` | `Core/PeirceAdjointCycle.ad_cube_eq_ad` and `ad_sq_eq_odd` | Identify its normalized tripotent projectors with the existing even and mixed Peirce parts, using real scalars where needed |
| A57 three projectors and nine corners | `[Ring A] [Algebra ℝ A]`, `t*t*t=t` | `TripotentPeirceProjectors`; `TripotentLeftRightPeirceProjectors.jointPeirce_reconstruction` and `jointPeirceProjector_adjoint_weight` | Reuse these actual normalized projectors; recover them from two orthogonal idempotents without a second projector API |
| A57 five components | Same full real algebra | `TripotentFiveGradingDecomposition.tripotentFiveGradeLinearEquiv` is already a genuine linear equivalence | Identify `fiveGradeRange t k` with the native eigenspace of `LieAlgebra.ad ℝ A t`; prove the missing converse |
| A57 quintic and grade closure | Same full real algebra; arbitrary operators | `Physics/TripotentAdjointDerivation` owns `adLinear`, the derivation law, and product/bracket weight addition | Bridge `adLinear` to native `LieAlgebra.ad`; prove the native endomorphism quintic and vanishing outside the five weights |
| Non-vacuity and geometric boundary | Full real 4-by-4 matrices | Existing matrix witnesses were inspected but do not combine the required properties | A non-diagonal tripotent, nonzero witnesses for every weight, noncommuting operators, and a noncommutative grade-zero corner |

The generic five-range owner imports `Mathlib` transitively. New modules use
focused direct imports; the exact verification closure must honestly include
that existing broad dependency. Do not rebuild its five-projector direct sum.

## Equations to prove

Write `δ(x)=x²-x`, `τ(t)=t³-t`. In an arbitrary associative ring:

* `δ(x+y)-δ(x)-δ(y)=x*y+y*x`.
* `δ(-x)+δ(x)=2 • (x*x)` and `δ(-x)-δ(x)=2 • x`.
* `δ(x)*δ(-x)=δ(x*x)`.
* `τ(t)=(t+1)*δ(t)=(t-1)*δ(-t)`.
* For `p²=p`, `δ(p+y)=y²+(p*y+y*p-y)`.
* The tangent equation is equivalent to vanishing of both diagonal Peirce
  corners and to reconstruction from the two mixed corners. Its square lies
  in the centralizer of `p`; iterating the defect preserves that property.
* With `E=u+v`, `J=u-v`, `K=u*v+v*u`, `C=u*v-v*u`, the unambiguous native
  correction equations are
  `-ad(C)^2(E)-ad(J)^2(E)=-4 • ((K*K-K)*E)` and
  `(ad(C)^2-ad(E)^2)(J)=4 • ((K*K-K)*J)`.
  The raw names `projPhi`, `derivSqSig`, and `derivSqJ` have no definitions in
  the searched Lean or Markdown source. These equations therefore receive
  mathematical names, not unsupported identifications with those macros.

For the existing normalized real projectors, with no tripotence hypothesis:

* `projPos(t)*projNeg(t)=(1/4) • (t*τ(t))`.
* `projZero(t)*projPos(t)=(-1/2) • (τ(t)*(t+1))`.
* `projZero(t)*projNeg(t)=(1/2) • (τ(t)*(1-t))`.
* `δ(projPos(t))=(1/4) • ((t+2)*τ(t))`.
* `δ(projNeg(t))=(1/4) • ((t-2)*τ(t))`.
* **`δ(projZero(t))=t*τ(t)`**, with a positive sign.

For `t³=t`, set `D=LieAlgebra.ad ℝ A t`. The required native operator identity
is `D^5 - 5 • D^3 + 4 • D = 0`. The five existing ranges are exactly
`Module.End.eigenspace D (fiveGradeValue k : ℝ)`. Products and Lie brackets
add weights, and weights outside `{-2,-1,0,1,2}` have zero eigenspace.
The direct decomposition already in the repository is reused rather than
restated as a theorem-shaped record of assumed conclusions.

## Proof dependency order

This is a dependency partial order, obtained by transitive closure of proved
prerequisites; the arrows assert actual use, not analogy. Final documentation
will replace planned edges by the checked declaration/module dependencies.

1. Associativity and native ring/linear-map operations support defect calculus.
2. Idempotence and existing Peirce support laws support tangent cancellation.
3. Opposite-corner multiplication laws support the quadratic frame and native
   double-adjoint corrections.
4. Closure under ring operations supports finite iteration and native
   subalgebra inclusion. This branch does not require a spectral theorem.
5. Off-shell tripotent identities specialize at `τ=0` to the existing
   normalized projector resolution.
6. Left/right projector composition supports nine corners and their weights.
7. Reconstruction and weight separation support the native eigenspace
   identification; the five weights annihilate the quintic.
8. Explicit full matrix operators instantiate these generic results and prove
   that every weight can occur and that grade zero need not commute.

## Corrections and scope boundaries

* The zero-projector defect sign in the source prose is wrong; use the positive
  identity above. Preserve the original source through its pinned provenance.
* `t²±t` are twice the real projectors. They are not idempotents in general.
* Polarization is a quadratic second difference. The linearization at `p` is
  `y ↦ p*y+y*p-y`; a Fréchet derivative theorem would require a named topology.
* A square map cannot recover the orientation of multiplication: an algebra
  and its opposite have the same square map. No universal recovery of the
  oriented commutator from `δ` is claimed.
* Iteration stays in a single-generator polynomial subalgebra. It neither
  proves infinitely many independent operators nor creates new adjoint weights.
* A five-weight decomposition is not by itself an `su(3)`, TKK, root-system,
  mass-gap, or physical classification theorem. Grade zero can be nonabelian.
* Self-adjointness and orthogonal geometry require explicit star hypotheses.

## Acceptance requirements

Generation, independent semantic audit, and independent runtime acceptance
are separate roles. The accepted artifact must have complete proofs, no
`sorry`/`admit`, no custom axioms, no `unsafe`/`partial`, no `native_decide`,
and no hidden theorem fields. Only the standard Mathlib axiom footprint is
allowed. Run strict Lean checks of every touched owner, a native isolated
Lake build of its exact repository import closure, exhaustive closure axiom
inspection, placeholder/vacuity/constructivity gates, and source hash checks.

All compilers share `/tmp/info-geometry-build.lock`. The unchanged pins are
Lean `4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
This scoped build is not a claim that the unrelated root package builds.

The bounded repository preflight found no generated declaration DAG, InfoTree,
or local LeanSearch index in this checkout. Source navigation is the evidence;
no stale graph or imagined live Arango result is used for theorem authority.
