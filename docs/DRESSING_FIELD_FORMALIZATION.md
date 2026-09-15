# Conditional dressing and relational coordinates

## Source and convention

The supplied Ravera interview motivates conditional construction of invariant
composites, changes of physical reference frame, and point-coincidence
readouts. Advertisements and biographical passages have no mathematical role.

[Berghofer and François, *Dressing vs. Fixing*](https://arxiv.org/html/2404.18582v2),
section 2.2, supplies the dressing transformation law and distinguishes
dressing fields from gauge-group elements. The algebraic extraction here uses
a **left action**: `frame(g • configuration) = g * frame(configuration)` and
`field(g • configuration) = g • field(configuration)`.
Consequently `frame(configuration)⁻¹ • field(configuration)` is invariant.
To compare with `u^γ = γ⁻¹u`, take the acting parameter to be `g = γ⁻¹`.
This is a convention translation, not a construction of a principal bundle.

## Repository search and reuse

Before editing, content searches ran recursively over the working tree,
including hidden/ignored and recovered/archive Lean files, excluding Git
metadata. The broad dressing/gauge/orbit/cocycle query returned 14,844 matching
lines; the focused dressing/frame-change query returned 32. These counts
include duplicated recovery copies, not independent theorems. Search logs:
`/tmp/dressing-content-hits.txt` and `/tmp/dressing-specific.txt`.

Inspected owners include:

- `Projective/Rays.lean`: native `MulAction.orbitRel` for real-scaling rays.
- `Projective/PhysicalKinematics.lean`: invariant-observable descent for that
  particular doubled-space action.
- `Optics/LocalGaugeGroupAction.lean`: a native group action on complete
  algebraic connection structures, including the inhomogeneous term.
- `Optics/OperatorQGTGaugeModuli.lean`: specialized connection orbit quotients.
- `Canonical/BogoliubovBerryMaurerCartanBridge.lean`: existing algebraic
  Maurer–Cartan and covariant-derivative identities.

The new owner `Geometry/DressingField.lean` uses Mathlib's `MulActionHom`,
`MulAction.orbitRel`, `Quotient.lift`, and `Equiv`. It does not replace the
existing connections, quotients, or differential operators. Its group/action
parameters permit specialization to existing action instances without building
a second connection algebra. Such a specialization has not been compiled here;
the local-gauge owner has a 273-name non-Mathlib import closure.

## Proven scope

- Equivariant frame and field imply invariant composite and unique quotient
  descent for that composite.
- The relative frame `first⁻¹ * second` is invariant, satisfies the transition
  cocycle law, and transports the dressed field between reference frames.
- A global group-valued equivariant frame forces every stabilizer to be trivial.
  A nonidentity symmetry fixing a configuration therefore obstructs such a frame.
- Normalizing a configuration is idempotent and separates exactly the orbits
  when such a global frame exists. Arbitrary dressed matter readouts need not
  separate orbits.
- Pulling a field into bijective reference coordinates is invariant under
  simultaneous relabelling of field and reference coordinates.
- `DressingFieldDependency.lean` verifies a finite dependency partial order
  with parallel branches; it does not inspect Lean's environment.

The global-frame hypothesis is substantial. No theorem asserts that all gauge
theories admit one. The normal-form theorem is set-theoretic and does not
establish a smooth global section, evade Gribov–Singer obstructions, or identify
dressing with gauge fixing. Reference-coordinate maps are assumed bijective;
singular, local, and noninvertible clock fields require further domain data.

No claim is made about BRST ghost cancellation, quantum anomalies, existence of
path-integral measures, dynamics, or a solution of quantum gravity. No smooth
bundle, connection, or quantum measurement theory is defined by this extension.

## Validation

Narrow serial checks use the shared build lock and the installed Lean 4.28.0
with cached Mathlib, writing only isolated build outputs. The pinned Lean 4.28.1
is unavailable; no toolchain or dependency metadata was changed. The checks are
not a full repository build or a pinned-toolchain validation.

All three new Lean modules compile in that environment. The seven regression
examples pass. Axiom checks cover all 18 new theorems and the quotient-lift
definition: only `propext`, `Classical.choice`, and `Quot.sound` occur, or subsets
thereof. No `sorryAx`, custom axioms, or `native_decide` are used.
