# Real Krein Peirce sections over the Klein double cover

## Intake and scope

The requested bridge joins the existing doubled real Krein carrier, the free
Klein deck action, and Peirce naturality in an algebra of continuous equivariant
sections, with the compatibility `rho ∘ Pi = Pi ∘ rho`.

Source baseline: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
Environment: the checked-in `lean-toolchain` and `lake-manifest.json`; no
dependency or toolchain changes are part of this task.

This is a topological operator-algebra construction. It retains arbitrary
complete real Hilbert fibres and noncommutative continuous endomorphisms.
It does not assert a physical CPT theorem, a differential operator, bundle
local triviality, or an analytic modular-flow construction.

## Existing owners

- `Core.PeirceGrading`: division-free even/odd Peirce projections, reflection,
  its conjugation action, and their laws under idempotence.
- `Core.PeirceStarNaturality`: reflection and corner naturality for ring maps.
- `OperatorAlgebra.RealDoubledChiralKreinComplements`: continuous left/right
  projectors, their complementary laws, isotropy, and exchange by `etaChiral`.
- `OperatorAlgebra.RealDoubledChiralKreinNative`: the real isometric swap and
  the explicit cross-pairing `InfoGeometry.Krein.KreinSpace` value.
- `Topology.KleinGlideCovering`: the free `ZMod 2` action on the real torus and
  its actual quotient covering map.
- `Topology.KleinRealOperatorDescent`: the existing descent API for invariant
  all-function fields. The current task supplies continuous, twisted algebra
  sections and does not identify those two different carriers.

Owner search also inspected the complex-valued `KleinAssociatedSpinors` and
`KleinBottleSpinorGlide` section APIs. They do not provide the requested real
continuous operator subalgebra.

## Claim ledger and theorem contract

1. **Generic associative-ring identity.** For a ring endomorphism `rho` and an
   element `p` satisfying `rho p = 1 - p`, prove that `rho` negates the existing
   Peirce reflection and commutes with its conjugation, even, and odd maps.
   This identity does not need idempotence or commutativity. Idempotence is
   required separately for projection and involution laws.
2. **Continuous section carrier.** Construct a native
   `Subalgebra ℝ C(X, A)` of continuous maps `a` satisfying
   `a (g x) = rho (a x)`. The algebraic carrier needs a real algebra
   automorphism `rho`; continuity and involution of the concrete deck action
   are supplied by the actual Klein/Krein owners.
3. **Parity on sections.** Use claim 1 to restrict the existing pointwise
   Peirce operators to that subalgebra. Prove continuity, real linearity,
   complementary projection laws, and multiplicative involutive grading
   when `p` is idempotent.
4. **Constructed real instance.** Set `X = BrillouinTorus`, `g = torusGlide`,
   `A = DoubledSpace E →L[ℝ] DoubledSpace E`, and `p = leftChiralProjector`.
   Construct `rho` by conjugation with the existing `chiralSwapLIE` and prove
   its sheet-exchange hypothesis from the existing complementary projector
   theorems. Identify the pointwise reflection with `gamma5`.
5. **Nonvacuity.** Construct the constant identity and mirror sections; under
   `Nontrivial E`, prove a nonzero section. Keep base equivariance distinct
   from a pointwise fixed-vector condition.

The input law in claim 1 is an explicit conditional hypothesis. Claim 4 must
derive that law for the concrete real carrier; it may not store the requested
commutation theorem as a structure field.

## Dependency order

`PeirceStarNaturality` → `PeirceSheetExchange` →
`ContinuousPeirceSections` → `KleinRealKreinPeirceSections`.

The final instance additionally imports the existing continuous real Krein
and genuine Klein covering owners. Its fields are maps on the covering torus
with the stated transition law; no new quotient relation is introduced.

## Validation plan

- Compile the new owners and their actual local import closure with the
  pinned Lean/Mathlib environment, under the shared build lock.
- Run the maintained locked Lake/file entrypoints and record their actual
  coverage or infrastructure failures.
- Inspect all new declaration axiom dependencies; only `propext`,
  `Classical.choice`, and `Quot.sound` are permitted.
- Run placeholder, staged-proof, and semantic-vacuity checks.
- Obtain independent semantic review of the final source; generation,
  semantic audit, and final build acceptance remain separate responsibilities.
- Publish the reviewed change as a PR with the observed build scope and any
  inherited repository-wide validation debt stated explicitly.

Validation results are recorded in the PR after execution; this contract is
not evidence that any planned check has already passed.
