# Lie–Jordan, Peirce and Clifford operator synthesis

## Intent and carriers

Compile the two preserved streams into complete native Lean 4 / Mathlib proofs.
The algebra carrier is an arbitrary associative unital algebra `A` over a
commutative ring `R`; the matrix realization is the full `Matrix n n ℂ` for
arbitrary finite `n`. Lie–Jordan maps live in `Module.End R A`.
The Clifford construction lives in `Module.End R (M × M)` for an arbitrary
module `M`, and is instantiated with `M = Matrix n n ℂ`. No commutation of input algebra elements or operators, and no
diagonalizability, is assumed. Matrix superoperators are never
replaced by the coefficient matrices acting on column vectors.

Lean: `leanprover/lean4:v4.34.1`. Mathlib:
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Do not modify these pins.

## Owner contract

- `Core.JordanMultiplicationClosure.jordanLeft` owns `X ↦ SX + XS` as an endomorphism.
- Mathlib `LieAlgebra.ad R A` owns `X ↦ HX − XH`.
- `Core.JordanAssociator.commutator_symm_operator` owns the mixed elementwise identity.
- `Core.JordanAssociator.symm_operator_commutator` owns the Jordan/Jordan identity.
- `Core.PeirceDecomposition.component10/component01` own the directed corners.
- `Core.PeirceGrading.odd`, `.reflection`, `.odd_reconstruction`, `.corners_sq_zero`,
  `.mem_odd_iff`, `.isCompl`, `.decomposition` own parity and algebraic tangency.
- Native `LinearMap.prod`, `.coprod`, `.prodEquiv`, `.coprodEquiv` supply full operator blocks.
- Native `Matrix.trace`, `.traceLinearMap`, `.conjTranspose`, `.PosSemidef` supply
  the matrix pairing and positivity. No replacement matrix or scalar carrier.

Existing trace consumers include `Physics.MatrixTraceBimodulePairingNative` and
`Physics.MetriplecticDynamicsDrivers`; existing parity consumers include
`Core.NilpotentToCartanDrazinMPPoset` and `Canonical.CattoGurseyBlockGrading`.
These owners and definitions are preserved. New consumers are the synthesis modules
below. The new layer lifts existing pointwise identities to native operator equalities.

## Missing theorem contracts

1. `Core.LieJordanComposition`: bundled mixed and Jordan brackets; exact ordered
   products `(ad H − J S)(ad H + J S)` and its reverse, retaining respectively
   `+ J [H,S]` and `− J [H,S]`; commutation detection under explicit cancellation
   of doubling; cyclic biadditive trace adjunction and exact trace shifts.
2. `Core.OperatorCliffordDouble`: full four-block linear equivalence, faithful
   simultaneous lift, concrete square-one anticommuting generators, structural
   commutation of lifts with the two constructed gamma generators, and all four square/mixed-product formulas for
   `[[A,B],[B,−A]]` and `[[A,−B],[−B,−A]]` on the doubled module.
3. `Core.PeirceStarCharges`: link existing corners to native `[p,a]` and `odd p a`;
   opposite squares, anticommutation and nilpotent sum. Under `IsStarProjection p`
   and self-adjoint `a`, prove adjoint parities. For full complex matrices, prove
   that `odd p a` and `I • [p,a]` are Hermitian, have the same positive semidefinite
   square, and anticommute. Preserve a nonzero criterion via `[p,a] ≠ 0`.
4. `Canonical.LieJordanMatrixGeometry`: full-matrix bilinear trace form and its
   nondegeneracy; genuine conjugate-transpose trace adjunction; actual Lie–Jordan
   superoperators as inputs of the faithful Clifford double; a noncommuting
   full-matrix realization/witness for the retained correction and Peirce sector.
   For `Hᴴ = −H` and `Sᴴ = S`, prove the negative quadratic trace identity
   `Tr(Xᴴ C−(C+ X)) = −Tr((C+ X)ᴴ(C+ X))`, with nonpositive real part;
   this is a pairing identity, not a pre-trace matrix equality.

Names will describe the exact proved algebra. Every theorem needs a proof term;
no placeholder, custom axiom, assumed conclusion, unsafe proof, or vacuous wrapper.

## Proof prerequisite partial order

`JordanAssociator + jordanLeft + native ad → LieJordanComposition`.
`native product/coproduct endomorphisms → OperatorCliffordDouble`.
`PeirceDecomposition → PeirceGrading → PeirceStarCharges`.
`LieJordanComposition + matrix trace → bilinear trace geometry`.
`LieJordanComposition + conjugate transpose → Hilbert–Schmidt trace adjunction`.
`PeirceStarCharges + native matrix Gram positivity → positive charges`.
`LieJordanComposition + OperatorCliffordDouble + full matrix carrier → synthesis`.
Edges are proof prerequisites, not analogies or temporal/physical causality.

## Atom classification and corrections

| Intake atom | Classification at intake | Formal disposition |
| --- | --- | --- |
| XXIV square and ordered cross products | local algebra, missing source definitions | explicit doubled endomorphism construction |
| XXV Peirce grading and square-zero sum | local algebra | reuse owners; add square and star bridges |
| XXVI/XXVII trace duality | local bilinear identity | cyclic trace; separate conjugate-transpose pairing |
| XXVIII unrestricted product sign | countermodel candidate | correct plus sign in minus-times-plus product |
| XXVIII commuting restriction | conditional specialization | retain arbitrary noncommuting coefficients |
| XXIX coefficient/superoperator substitution | invalid carrier identification | double the actual matrix superoperators |
| BKM / Amari / Levi-Civita / PDE assertions | open interpretation debt | excluded from theorem statements |
| Both Peirce D and M Hermitian | false without correction | use Hermitian `M` and `I • D` |

At intake, no attached code is classified as kernel verified. Final statuses must
be backed by the exact source hashes, build logs, declaration/axiom audit, and
independent semantic/acceptance reviews. Raw intake remains preserved verbatim.

## Acceptance and limits

Compile exact repository source closure and narrow Lake targets with the pinned
compiler, under the shared build lock and with no concurrent compiler. Audit all
new declarations and imported repository source closure for placeholders and
axiom dependencies. Allowed foundational axioms are `propext`, `Classical.choice`,
and `Quot.sound`, reported explicitly. No root-package success may be inferred
from a scoped build. Preserve dependencies and caches.

The formal geometry is algebraic idempotent tangency, full matrix trace pairings,
star projections and positive semidefinite Gram operators. No manifold connection,
state-dependent BKM metric, unbounded operator domain, geometric curvature/PDE,
or continuum theorem is asserted. These interpretations remain
`[bucket_3_open_debt]`; hypotheses such as self-adjointness and cancellation of two
are `[bucket_2_conditional]`, stated in the theorem types.
