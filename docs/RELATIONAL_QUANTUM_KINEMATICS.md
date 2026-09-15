# Particle reference frames and cocyclic dressing

## Source and extraction

The supplied Ravera QFM seminar is the primary extraction input. The companion
paper is J. T. François and L. Ravera,
[Relational bundle geometric formulation of non-relativistic quantum mechanics](https://arxiv.org/html/2501.02046v2).
The extracted mathematical content is common-translation reduction, particle
reference frames, action-dependent cocycles, and phase transport. Biographical
and interpretative assertions are not theorem hypotheses or conclusions.

This implementation uses left actions, with the explicit convention

`C(g * h, x) = C(g, h • x) * C(h, x)`.

A frame satisfies `frame(g • x) = g * frame(x)`; dressing evaluates at
`frame(x)⁻¹ • x`. For additive translations this is precisely subtracting the
reference particle's position. A particle reference is an explicit argument;
there is no hidden assumption that an empty particle type has a reference.

## Search and reuse

Before writing code, recursive content searches included hidden, ignored,
recovered, and archived Lean sources, excluding Git metadata. The focused
cocycle/particle-reference search returned 212 lines, including recovery copies.
Search outputs are `/tmp/relational-qm-content-hits.txt` and
`/tmp/particle-reference-hits.txt`. These are navigation evidence, not a claim
that every matching file supplies an independent formal theorem.

Reused owners:

- `Geometry/DressingField.lean`: native equivariant frames, normalization,
  translation-orbit separation, and invariance.
- `Canonical/Algebraic/ModularRotorCocycle.lean`: `MulActionCocycle`.
- `Cocycle/ActionCocycle.lean`: the existing coboundary constructor.
- Mathlib: pointwise actions, `Multiplicative`, `MulActionHom`, `Circle`,
  `Circle.exp`, and norm preservation under the native circle action.

No new cocycle structure, group action implementation, principal connection,
or copy of the existing normalization theorem is introduced.

## Modules and dependency order

- `Geometry/ParticleReferenceFrames.lean` constructs particle evaluation frames,
  proves relative-coordinate identities and time-dependent common-translation
  invariance, and characterizes equality of relative coordinates by a common
  translation. Independent particle translations need not preserve shape.
- `Geometry/CocyclicDressing.lean` proves the dressing formula from cocyclic
  equivariance and the noncommutative frame-transport composition law. It
  instantiates the existing coboundary with `exp(-action / hbar)` in `Circle`.
- `Geometry/RelationalQuantumKinematics.lean` supplies concrete complex phase
  waves and proves particle-frame covariance and pointwise norm preservation.
- `Geometry/RelationalQuantumDependency.lean` proves a finite partial order:
  frame existence precedes normalization; frame existence and the action
  cocycle precede transport; transport precedes circle-norm preservation;
  normalization and norm preservation meet at particle-wave covariance.
  Normalization and the action cocycle are incomparable branches. This is an
  explicit mathematical dependency model, not Lean-environment introspection.
- `Geometry/RelationalQuantumKinematicsTests.lean` exercises integer particle
  positions, genuine internal shape changes, arbitrary moving translations,
  action-dependent phases, and coefficient groups not assumed commutative.

For transport from frame `first` to `second`, the group element is
`second(x)⁻¹ * first(x)`, evaluated by the cocycle at the first normalized
configuration. Composition is in the order `second→third` times `first→second`.
This order matters for noncommutative coefficient groups.

## Scope boundaries

`action` is an arbitrary real-valued function, not a constructed Hamilton
principal function. `hbar` is a real parameter; algebraic identities use Lean's
total division and hold even at zero. Physical use requires positive `hbar`.
The phase waves are explicit examples, not a classification of all wavefunctions.

No theorem derives a Schrödinger equation, canonical momentum operator,
Euler–Lagrange equation, flat differential connection, or path-integral measure.
Those require additional differential and dynamical data. Pointwise norm
preservation does not establish an operator on a global Hilbert space of
wavefunctions. Setting one relative coordinate to zero does not prove that the
reference particle is classical or lacks quantum properties. This extension
does not claim new identifications with nuclear chirality or the QPM.

## Verification environment

Verification uses serial, shared-lock, isolated checks with installed Lean
4.28.0 and cached Mathlib. The pinned Lean 4.28.1 is unavailable locally. No
toolchain, dependency source, manifest, or cache is changed. This is not a
pinned-toolchain or full-repository build.

All five Lean modules compile in that isolated environment. All eight regression
examples pass. Axiom audits of all 25 new theorems report only subsets of
`propext`, `Classical.choice`, and `Quot.sound`: no `sorryAx`, custom axioms, or
`native_decide`. The action-cocycle owner and its prerequisite were also compiled
before reuse. Targeted staged-diff whitespace checks pass.
