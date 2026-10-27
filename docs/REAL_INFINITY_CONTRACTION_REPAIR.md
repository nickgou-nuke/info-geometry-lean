# Real infinity rotation and genuine exterior contraction

## Ground-truth theorem contract

This continuation responds to the attached source audit while preserving the
user's requirement of intrinsically real carriers and genuine algebraic duals.
It extends PR #227. PR #228 is inspected as a separate source of conventions;
its complex Lorentz-slice modules are not imported into the new construction.

Two source-confirmed gaps are addressed:

1. `Canonical/ExteriorContractionOperatorBridge.contractionOp` was literally
   the zero linear map. The repair replaces it on the same generic exterior algebra with
   Mathlib's actual zero-quadratic-form contraction, already used by the real
   `KahlerAtiyahCartanForms` owner. Repair dependent proofs that unfolded the
   zero implementation and prove genuine mixed CAR and number-operator action.
2. Connect the actual real twistor block rotation to its six Plucker minors,
   the inverted incidence plane and an explicitly compatible native Clifford
   automorphism. Retain the exact real signs and prove the obstruction to the
   attachment's proposed identification with the global sheet reflection.

## Scalar and sign conventions

The existing real twistor carrier is `Spinor × Spinor`, with
`Spinor = Fin 2 → ℝ` and incidence `(X π, π)`. The real rotation is

`R₀(ω,π) = (π,-ω)`, so `R₀² = -id`.

Its action on the existing Plucker coordinate order `(01,02,03,12,13,23)` is

`T(P) = (p23,p02,p12,p03,p13,p01)`, so `T² = id`.

For the graph frame, the target is

`T(P(X)) = det(X) P(-X⁻¹)` when `det X ≠ 0`.

The attachment's complex map `(-iπ,iω)` induces `-T`, with the opposite
homogeneous prefactor. Those are distinct linear maps, even though their
projective bivector actions agree. No complex scalar or restriction of
complex scalars is used in the new implementation.

The real Klein form is `q(P) = p01*p23 - p02*p13 + p03*p12`. For
`P=(a,b,c,d,e,f)`, the proposed native embedding has positive components
`((c+d)/2, (b-e)/2, 0, 0, (a+f)/2)` and negative components
`((d-c)/2, (b+e)/2, 0, 0, (f-a)/2)`. Its quadratic form is exactly `q(P)`.
The rotation `T` corresponds to flipping negative modes 0 and 4. The target
automorphism therefore reuses the existing `negativeReflectionAlg 0` and
`negativeReflectionAlg 4`.

The global sheet reflection fixes only vectors with nonnegative native
quadratic norm. In contrast, `T` fixes `(0,1,0,0,1,0)`, whose Klein value is
`-1`, and `(1,0,0,0,0,1)`, whose Klein value is `1`. These witnesses obstruct
the proposed global-reflection intertwiner for either overall quadratic sign.
The witnesses have nonzero Klein value. This is an obstruction on the whole
quadratic carrier; it does not rule out maps restricted to null/decomposable
bivectors or projective correspondences.

## Glide reflection and the retained spinor sign

The user's continuation explicitly requires the glide/Moebius twist. The
existing `Topology/KleinQuotientDeckInvariants` owner supplies the genuine
affine action, not just its orientation character:

`deckB(x,y) = (-x,y+1)`, with `deckB²(x,y) = (x,y+2)`.

It also supplies the half-shift convention and the exact coordinate rescaling
between half-shift and unit-shift glides. These owners must be reused.

The chosen spinor lift of the glide carries the same base displacement and
the actual real block rotation on its fibre. Its target square is

`G_spin²((x,y),z) = ((x,y+2),-z)`.

The induced bivector/Clifford lift instead has

`G_Cl²((x,y),A) = ((x,y+2),A)`.

The difference records the spinor sign lost on taking the second exterior
power. A total glide has no fixed point because of the nonzero base shift;
it is not an involution on the covering space. The nonzero infinity-minus-origin
channel changes sign under its fibre automorphism. This is the explicit sign
representation needed for a twisted real line. The plus channel is invariant.

The global-reflection obstruction above concerns an isometric intertwiner of
specified linear carriers. It does not exclude an affine glide, a nontrivial
bundle holonomy, or a different spin/Pin lift. The new construction must state
its chosen fibre representation and prove its group/action laws. A geometric
spin/Pin structure or associated-bundle quotient is not constructed here.

A separate narrow bridge reuses `Clifford/Cl55WittPinAction`: the native
`Pin55` element `r = fNegPin 0 * fNegPin 4` has exactly `F04` as its twisted
vector action, and its actual Clifford square is `-1`. The algebraic Pin lift
is therefore explicit. Its central sign must be retained: the existing
`AffinePin55Cover.affinePinGlide_square` theorem assumes `r*r = 1`, which is
not the relation of this element. Identifying the four-real-dimensional
`R0^n` fibre with a representation sector of the native exterior Pin spinors
still requires an explicit intertwiner; equal square signs alone do not give
that identification.

The reused base owner carries Klein deck data. The Moebius feature recorded
here is the sign monodromy along the orientation-reversing generator. A
Moebius-strip quotient or a quotient-space identification is not part of this
finite algebraic construction.

The genuine dual fibre is `TwistorSpace × Module.Dual ℝ TwistorSpace`.
Its covectors transform by precomposition with the inverse twistor map. The
existing neutral and symplectic forms and the evaluation incidence constraint
are invariant. Two glides negate both the primal and covector components.
The symmetry action uses `frameAction`, kept distinct from the self-adjoint
`dualLift` used by the sector Hamiltonians.

## Existing owners reused

- `Twistor/RealTwistorIncidence` and `RealTwistorSoldering`: actual real
  incidence submodules and spinor endomorphisms.
- `Projective/KleinQuadricPlucker`: the established six minors, quadratic
  form, polarization and separate homogeneous scaling.
- `Clifford/Cl55WittOrthogonalReflections`: actual vector isometries and
  induced native Clifford algebra equivalences.
- `Canonical/Cl55InfinityWittBoundary`: normalized native infinity/origin
  vectors, CAR and affine coordinate readouts.
- `Topology/KleinQuotientDeckInvariants`: existing semidirect deck group,
  affine action, glide square and half-shift normalization. The different
  `Canonical/KleinDeckFiveGradeAction` representation remains distinct until
  its Clifford carrier is connected by a separately proved intertwiner.
- `Canonical/KahlerAtiyahCartanForms` and Mathlib Clifford contraction:
  genuine exterior multiplication and contraction.
- Existing categorical/tensor-colimit owners retain their universal role;
  no continuum, GNS, KMS or amplitude correspondence is claimed by these
  finite algebraic compatibility results.

The `PlanePoint` Klein cover and the real matrix incidence chart are separate
carriers. The total glide is a chosen fibre representation over the former;
its base glide is not identified with `X ↦ -X⁻¹` or with a full
spacetime conformal action. The nonzero odd line exhibits the sign information.
A square-minus-identity fibre operator by itself does not prove nonorientability
of the whole twistor bundle.

## Source map and operator scope

| Owner | Concrete result |
| --- | --- |
| `Twistor/RealTwistorBlockInversion` | Real block automorphism, its square, native incidence-plane image, signed graph inverse chart |
| `Twistor/RealPluckerCl55Reflection` | Injective native quadratic embedding, actual Clifford anticommutator and partial-reflection intertwiner, whole-carrier global-reflection obstruction |
| `Twistor/RealTwistorPinReflection` | Actual native Pin product realizing `F04`, its vector/Plücker action and Clifford square `-1` |
| `Twistor/RealTwistorExteriorReflection` | Literal `exteriorPower.map`, universal-property intertwining on all bivectors, native quadratic and Clifford compatibility |
| `Twistor/RealInfinityTwistor` | Actual map to the algebraic dual, alternating form, exact radical, nonzero witness and native infinity readout |
| `Twistor/RealTwistorGlideHolonomy` | Full affine action, translated square/fourth powers, actual Clifford involution and nonzero odd channel |
| `Twistor/RealTwistorGlideDual` | Contragredient action, both dual/primal minus signs, neutral/symplectic/constraint invariance |
| `Canonical/ExteriorContractionOperatorBridge` | Genuine contraction, generator/product rules, mixed CAR as endomorphisms, faithful and nonzero action |
| `Canonical/FockNumberOperatorBridge` | Actual occupied-state action, `N² = alpha(u) N`, normalized nonzero idempotency |
| `Canonical/TwoParticleOperatorAnnihilationBridge` | Actual two-particle contraction with the fermionic minus sign |
| `Canonical/BerezinFermionicIntegrationBridge` | One selected contraction direction, vacuum zero, normalized generator sent to the unit |
| `Canonical/ExteriorContractionNativeCompatibility` | Equalities with the existing real Kähler--Atiyah operators on the same carriers |

The normalization `alpha(u) = 1` is a dual-pairing condition. It makes the
occupation map idempotent and nonzero over a nontrivial ring; it does not by
itself make an arbitrary such projector orthogonal or Krein self-adjoint.
The physical positive normalization of the earlier stationary sector remains
in `REAL_TWISTOR_SECTOR_ACTION.md` and uses its separately constructed metric.
The one-mode Berezin operation has exterior-algebra codomain; integration over
all modes or a scalar top-degree integral is not supplied here.

Harmless legacy scalar-evaluation theorem signatures are retained. Their
presence does not upgrade unrelated scalar Wick/CAR packets or existing
conditional Hodge identities into new operator or analytic theorems.

## Acceptance obligations

The implementation must include nonzero contraction/occupied-state witnesses,
actual evaluated mixed CAR, the exact real block/Plucker/Clifford compatibility
and the wrong-global-reflection obstruction. Audit all direct contraction
consumers for dependence on the old zero definition. Preserve harmless legacy
evaluation theorem names, while distinguishing them from new operator claims.

Use unchanged dependency pins, serial native Lean checks under the shared
build lock, independent semantic review and independent proof QA. Record the
actual verified scope and any root-package limitations after checking.

## Verification on 2026-10-27

The final serial native check passed using Lean 4.34.1 and the unchanged
Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. The disposable
runner acquired the repository's shared build lock, compiled actual source
imports, and matched each cached output against source/dependency hashes.

- The integrated `InfoGeometry.Physics.NuclearTwistorSectorAudit` has **179
  repository source modules** in its import closure. None of its source imports
  uses an alternate Architect checkout, Atlas, or GIFT.
- All **30 nonaggregate direct contraction consumers** were checked: 29
  preexisting consumers and the new native compatibility module. Together
  with the integrated audit, the **31 requested targets** span **209 repository
  source modules**. This whole native run passed.
- All **135 axiom-footprint queries** (83 retained and 52 new) returned only
  `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. No query
  returned `sorryAx` or a custom axiom.
- The final affected-source run had **zero errors and zero warnings**.
  Initial compilation of reused owners emitted preexisting deprecation/style
  lints; those unrelated dependency sources are unchanged.
- `tools/quality/proof_proxy_staged_gate.py` passed.
- `tools/infra/axiom_audit.py --fail-on-gaps` checked all **49 PR-changed Lean
  files**: zero explicit `sorry`, `admit`, or axiom gaps.
- `git diff --cached --check` passed. The toolchain, Lake configuration, and
  dependency pins have no changes relative to the PR base.

Independent source review accepted the real signs, complete exterior-power
intertwiner, dual action, native Pin product, and operator repair. The separate
consumer review read all 29 preexisting nonaggregate consumers and the new
compatibility module. Native compilation also required explicit scalar/module arguments in several
applications. The existing full-CAR lemma received this elaboration repair
without changing its theorem statement.

The two aggregate direct importers, `InfoGeometry.AllExhaustive` and
`InfoGeometry.Canonical.All`, remain part of the unverified root-package
boundary. As recorded in the earlier PR validation, the root environment lacks
the authentic Atlas path and initialized GIFT dependency and has the existing
broad Architect/toolchain incompatibility. This native 209-module check does
not claim a complete root Lake build or full publication-gate pass.
