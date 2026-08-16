# Erlangen 2.0 — theorem-honest manifest

> Status: documentation layer over kernel-checked owners
> Version: 1.0.0
> Date: 2026-08-15

## Core thesis

**Erlangen 2.0 replaces primitive point geometry by symmetry-adapted carriers,
represented operator algebras, invariants, and intertwiners.**

This is a description of the formal architecture, not a claim that scalar
coordinates cease to exist.  The primary generators live in Witt and
split-octonion carriers; they become operator coordinates only after a stated
representation such as `L_x`, `R_x`, `c(x)`, or `ρ(x)` is supplied.

## Status vocabulary

- **THEOREM** — a proposition checked by the Lean kernel in a named owner.
- **INTERPRETATION** — a geometric or physical reading of one or more theorems.
- **OPEN IDENTIFICATION** — a bridge still requiring a concrete map, hypothesis,
  or representation theorem.

## Typed Erlangen datum

The formal interface is the six-field record
`Erlangen20Datum (R V 𝔤 𝒮 ℐ)`, owned by
`Canonical/Erlangen20OperatorGeometryDatum.lean`:

`(V, operatorAlgebra, 𝔤, representation, symmetryData, invariantData)`.

The representation is a native Lie hom into `End(V)`, and
`representation_mem` explicitly records that its image lies in the selected
associative operator algebra.  Carrier intertwiners are separate records; the
generic theorem `OperatorIntertwiner.target_eq_conjugated` prevents an
unmentioned identification of unrelated carriers.

## Theorem layer

### Carriers and quadratic sectors

- **THEOREM:** the Witt carrier is an algebraic model of the form
  `V ⊕ V*`; no manifold or tangent-bundle structure is implied.
- **THEOREM:** the exchange fixed sector is four-dimensional and carries the
  quadratic form of signature `(1,3)` in the fixed-section owners.
- **INTERPRETATION:** this fixed sector may be read as an emergent Minkowski
  sector.
- **OPEN IDENTIFICATION:** a claim `W₄,₄ ≅ TM ⊕ T*M` would require an actual
  manifold, bundles, and a soldering theorem.

### Peirce/tripotent operator calculus

- **THEOREM:** `A^3 = A`, `F_P = A^2`, `P₀ = I - F_P`, and
  `range P₀ = ker A` in the corresponding owner hypotheses.
- **THEOREM:** `M = I - 2 F_P`; `M` is the Peirce parity, while `F_P` is the
  occupation projector.
- **THEOREM:** the Cayley–Hestenes relation is
  `C * K_W = - M * K_W * C`.
- **THEOREM:** on the `M = +1` sector, `C` is `K_W`-antilinear; on the
  `M = -1` sector, it is `K_W`-linear.
- **INTERPRETATION:** this is a sector-dependent real-structure statement.
- **OPEN IDENTIFICATION:** “antiunitary CPT” additionally requires explicit
  inner-product/Krein-isometry and Poincaré-action theorems.

### Exceptional and Clifford towers

- **THEOREM:**
  `Der(O_s) → so(4,4) → so(5,5)` through the stated linear and Lie maps.
- **THEOREM:** the carrier square satisfies
  `j (D w) = ι₅₅(D) (j w)`.
- **THEOREM:** the native spinor-lift owner transports Lie brackets, chirality,
  Hodge, and chiral-Dirac commutation from a supplied
  `Der(O_s) → SpinBivector55` lift datum.
- **THEOREM:** `G2Cl55FiniteHodgeEquivarianceDatum` packages the finite Lie,
  chirality, Hodge, and chiral-projector laws as a reusable datum.
- **THEOREM:** from `D_H² = 3I`, the finite normalized phase
  `F₃ = (1 / √3) D_H` satisfies `F₃² = I` and its kernel is invariant under
  the packaged action.  In fact, both the Hodge and normalized-phase kernels
  are proved trivial in the full finite master model.
- **INTERPRETATION:** any nontrivial topological or boundary index must use a
  restricted/boundary operator or a different Dirac realization; it cannot be
  attributed to the full finite master Hodge operator.
- **THEOREM:** `G2Cl55FiniteFredholmIndexBridge` packages the master operator
  as a finite `FredholmIndexDatum` and proves its ordinary algebraic index is
  zero, with both kernel and cokernel trivial.
- **THEOREM:** `RealCl55KasparovCycleBridge` records the finite bounded phase
  `F = D_H / 2`, its square `F² = 3/4 I`, chirality oddness, and (G_2)-spinor
  commutation.  This is a finite certificate; the nonzero square defect is not
  silently promoted to an analytic Kasparov class.
- **OPEN IDENTIFICATION:** this finite datum is not yet an analytic
  Kasparov `KK`-class; bounded transforms, compactness, and Kasparov products
  require separate analytic owners.
- **THEOREM:** every native spinor action lies in the strict Clifford bivector
  image, and its inverse matrix image has a bivector preimage; injectivity is
  inherited from injectivity of the supplied lift.
- **OPEN IDENTIFICATION:** the concrete native lift datum is still an input;
  no associative embedding `O_s ↪ Cl(5,5)` is asserted.

### Krein-to-Hilbert boundary

- **THEOREM:** `RealSplitKreinHilbertizationBridge` defines Hilbertization by
  composition with the fundamental symmetry `J` and proves the exact
  self-adjoint transport equivalence.
- **THEOREM:** the corresponding skew-adjoint transport is also available:
  `T♯ = -T` iff `(J ∘ T)* = -(J ∘ T)`.
- **OPEN IDENTIFICATION:** these adjoint transports do not by themselves
  provide regularity, a group integration, or a standard equivariant `KK`
  class.
- **THEOREM:** `FiniteCl55GroupEquivarianceSocket` packages a supplied group
  action as a `MonoidHom` into finite spinor endomorphisms and proves Hodge and
  chirality-kernel preservation from explicit covariance equations.
- **THEOREM:** `finiteG2HodgeDatumOfNativeLift` composes any supplied native
  `Derivation → SpinBivector55` lift with the finite Hodge datum, preserving its
  Lie, chirality, and Hodge covariance fields.
- **THEOREM:** `finiteKasparovPhaseOfNativeLift` is the direct normalized-phase
  constructor from that supplied lift; its involution, oddness, and Lie-action
  covariance are inherited by construction.
- **THEOREM:** `G2IntegratedKasparovEquivarianceBridge` transports the finite
  phase, its square, and its defect `I - F²` by conjugation under any supplied
  invertible group action; the canonical certificate has `I - F² = (1/4) I`.
- **THEOREM:** the same owner packages the supplied group action together with
  the finite phase, grading, square, and oddness laws as
  `FiniteGroupPhaseCertificate`.
- **OPEN IDENTIFICATION:** no concrete integration of the split real
  (G_{2(2)}) Lie action into such a group action is asserted by this socket.

### Arithmetic and thermodynamic layers

- **THEOREM:** finite character factors expand as
  `∏ (1 - χ(p) w_p) = Σ μ(n_S) χ(n_S) w_S` under the explicit prime and
  multiplicativity hypotheses.
- **THEOREM:** the standard `O₂` gauge convention has canonical inverse
  temperature `β_KMS = log 2` on the formalized word core.
- **OPEN IDENTIFICATION:** KMS, Tomita–Takesaki time, and geometric rapidity
  are distinct parameters until an explicit intertwiner identifies them.

### Operator functional calculus

- **THEOREM:** `ThreePillarMomentumIntertwinerBridge` packages conjugation by a
  carrier equivalence as an `AlgEquiv` on endomorphism algebras.
- **THEOREM:** `aeval` and polynomial annihilating relations transport in both
  directions; in particular, `p(P) = 0` iff `p(J P J⁻¹) = 0`.
- **THEOREM:** the induced momentum action is uniquely determined by its
  intertwining square.

## Interpretation layer

The corpus supports the following readings, provided they are labelled as
interpretations rather than promoted to theorems:

1. the exchange fixed sector is an emergent spacetime candidate;
2. `ker A` is an algebraic zero-mode carrier;
3. Peirce parity is a longitudinal/transverse grading;
4. split-octonion derivations act through the `so(5,5)` representation;
5. the tripotent sector and the Fibonacci categorical sector are compatible
   geometric/topological shadows only when a separate carrier intertwiner is
   supplied.

## Explicit firewalls

- Octonion associators, categorical Fibonacci associators, and Drinfeld
  associators are different operations.
- A Fibonacci braid theorem does not follow from octonionic nonassociativity.
- A zero-mode theorem does not by itself identify a physical horizon or an
  anyon Hilbert space.
- A finite inverse Euler-factor identity is `GL₁`-compatible arithmetic; it is
  not a proof of the Langlands correspondence.
- Lean verifies consequences of explicit definitions and hypotheses.  It does
  not establish that the physical interpretations are postulate-free.

## Remaining capstones

The current high-value open identifications are:

1. supply a concrete native `Der(O_s) → SpinBivector55` lift and its covariance;
2. identify a common carrier for modular, Cantor, and SUSY momentum actions;
3. prove the corresponding intertwining law before claiming conjugacy or
   literal operator equality;
4. only then compare Hodge/Dirac, KMS/modular, and geometric flows.

Until these are proved, the repository claims a collection of compatible,
kernel-verified finite interfaces—not a single completed physical theory.
