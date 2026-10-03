# Dirac Belt, Framed Ribbons, and Orientation-Reversing Gluings

## Scope

The Dirac belt trick is a mechanical visualization of the topology of the
rotation group.  Framing, Möbius strips, Klein bottles, and twist--writhe
relations provide useful geometric comparisons, but they are distinct
mathematical constructions and must not be identified without an explicit map.

This note separates the statements that are rigorous from the physical
interpretations that require additional hypotheses.

## 1. Framed ribbons

A framed curve consists of a centerline `r(s)` together with a transverse
vector `n(s)`.  A narrow ribbon is locally parametrized by

```text
R(s,v) = r(s) + v n(s).
```

The end identification

```text
(0,v) ~ (L,-v)
```

produces a Möbius strip.  Its transverse orientation reverses after one
longitudinal circuit and returns after two.  It is one-sided and has one
boundary component.

The orientation-preserving identification

```text
(0,v) ~ (L,v)
```

produces a cylinder.  Thus a full twist of a ribbon, by itself, is not a
construction of a Klein bottle.

A Klein bottle can be obtained by gluing two Möbius bands along their boundary
circles, or from the standard square quotient with one orientation-reversing
edge identification.  It has no boundary and cannot embed in ordinary
three-dimensional Euclidean space without self-intersection.

## 2. The belt trick and the rotation double cover

The belt trick concerns

```text
π₁(SO(3)) ≅ Z/2Z.
```

A rotation through `2π` represents the nontrivial loop in `SO(3)`, whereas a
rotation through `4π` is contractible.  Equivalently, under the double cover

```text
SU(2) → SO(3),
```

the `2π` rotation lifts to the central element `-1`, and the `4π` rotation
lifts to `+1`.

In a spin-`1/2` representation, the central element `-1` acts as minus the
identity.  This is the source of the spinor sign change.  The belt is a
classical visualization of the covering-space fact; it is not itself a proof
of the spin-statistics theorem.

## 3. Twist, writhe, and linking

For a sufficiently regular **closed** framed curve whose displaced boundary
curves are disjoint, the Călugăreanu--White--Fuller relation is

```text
Lk = Tw + Wr.
```

Here:

- `Tw` is the local rotation of the framing around the tangent;
- `Wr` is the global coiling of the centerline;
- `Lk` is the linking number of the two boundary curves.

Under an allowed deformation, `Lk` remains fixed while `Tw` and `Wr` may
exchange continuously.  Their changes depend on the chosen deformation and
framing; the numerical assertion `ΔTw = -2`, `ΔWr = +2` is not universal.

The ordinary belt demonstration has an open strip with fixed ends.  Applying
the closed-ribbon theorem therefore requires a closure convention or a
relative version of the invariant.  Writhe is a geometric curve invariant and
is not, in general, identical to orbital angular momentum.

## 4. Swept surfaces and glide identifications

A time-dependent ribbon sweeps out a surface in spacetime.  Its topology is
determined by its boundary conditions and quotient identifications.  It may be
a cylinder, annulus, Möbius-type surface, or another surface; it is not
automatically a Klein bottle.

A glide map such as

```text
(u, τ) ↦ (u + L, -τ)
```

must be specified as part of a quotient construction.  It does not follow
merely from observing a twisted belt.  Likewise, a CPT interpretation requires
an independently defined action and cannot be inferred from the ribbon
geometry alone.

## 5. Correct synthesis

The rigorous chain is

```text
belt motion
  → loop in SO(3)
  → lift to SU(2)
  → spinor sign under 2π
  → return under 4π.
```

Framing explains how a ribbon records transverse orientation.  Möbius and
Klein surfaces describe orientation-reversing gluings.  The
Călugăreanu--White--Fuller theorem describes the relation between twist,
writhe, and linking for closed framed curves.  These are compatible geometric
viewpoints, but they are not one theorem.

The spin-statistics theorem requires additional quantum-field-theoretic
assumptions.  No classical belt experiment, by itself, proves it or proves
that fermions are trajectories on a non-orientable Klein surface.

## Formalization boundary

A sound formal development should treat the following as separate layers:

1. quotient models of the Möbius strip and Klein bottle;
2. framed curves and the hypotheses of the twist--writhe theorem;
3. the covering map `SU(2) → SO(3)` and its `Z/2` monodromy;
4. representation-theoretic spinor phases;
5. any physical interpretation, stated only as an explicit conditional theorem.

No claim about zeta zeros, CPT, spin-statistics, or a Klein worldsheet should be
introduced without the corresponding carrier, action, and hypotheses.
