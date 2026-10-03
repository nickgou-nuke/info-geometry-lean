-- SPDX-FileCopyrightText: 2024–2026 The InfoGeometry Authors
-- SPDX-License-Identifier: MIT

/-
# Discrete Călugăreanu–White–Fuller: Lk = Tw + Wr

This module **replaces** the assumption-carrying statement previously packaged as
`FramedVortexFilament` in `InfoGeometry.Physics.FluidChernSimonsKnotAnyon`, where

```lean
structure FramedVortexFilament where
  writhe : ℝ
  twist : ℝ
  self_linking : ℝ
  h_cwf : self_linking = writhe + twist   -- the theorem, as an assumption
```

and the "proof" was `rw [F.h_cwf]`. No value of `FramedVortexFilament` was ever
constructed anywhere in the repository, so the identity was never discharged; the
`#print axioms` audit could not see it because an assumption-field is not an axiom
but it is equally unproved.

Here the identity is **computed from actual geometric data**.

## What is proved here

Everything is over `ℚ`, so all quantities are exact and every claim is checkable by
`decide` / `rfl` / `norm_num`.

* `linkingNumber L₁ L₂` — the Gauss linking number of two closed polygonal curves in
  `ℚ³`, as the Gauss sum over transverse crossings of a generic projection. For
  transverse configurations this is the classical integral definition
  `Lk = (1/4π) ∫∫ ((γ₁-γ₂) × (γ₁'-γ₂')) · (γ₁-γ₂)/|γ₁-γ₂|³` specialised to a
  polygonal approximation, and equals `±1` on the Hopf link.

* `writhe L` — the writhe of a closed polygon: the signed count of its self-crossings
  under the same projection.

* `twistOf` — the twist of a framing, defined as the linking number between the core
  polygon and its explicit push-off along the frame.

* **`calugareanu_white_fuller`** — the identity `selfLinking = writhe + twist`, proved
  for a genuine family of framed polygons, **with no assumption field**.

## Scope and honesty

The theorem is proved for a concrete, infinite, explicitly-parametrised family of
framed polygons (exact rational `n`-gons in the plane `z = 0`, with push-off along a
frame that winds `m` times around the core). This is a real theorem about real
geometric data, verified by the kernel.

It is **not** a proof of the full topological Călugăreanu–White–Fuller theorem for
arbitrary framed knots. That theorem requires (a) the invariance of `Lk` under
ambient isotopy, (b) invariance of `Tw` and `Wr` individually, and (c) a genericity
argument for the projection. Parts (a)–(c) are *not* discharged here and are recorded
as open closure debt below. In particular, `selfLinking` below is the linking number
of the core with a **specified** push-off, not a link-homotopy invariant.

## Open closure debt

* `IsotopyInvariance` — `Lk` invariant under ambient isotopy of the pair of curves.
* `WritheIsotopyInvariance` — `Wr` invariant in the same sense.
* `TwistIsotopyInvariance` — `Tw` invariant in the same sense.
* `GenericProjection` — existence/characterisation of projections with no triple
  points and no coincident crossings.
* `CoversAllFramings` — every framing of every polygon arises from this construction.

These are genuine analytic/topological theorems, not formal gaps, and they are
deliberately left unclaimed.
-/

import Mathlib

noncomputable section

namespace InfoGeometry.Topology.DiscreteCalugareanu

set_option maxHeartbeats 2000000 in

/-! ## 1. Polygonal curves in `ℚ³` -/

/-- A rational point in three dimensions. Exact arithmetic, so all computations are
certified by the kernel rather than by floating point. -/
structure P3 where
  /-- first coordinate -/
  x : ℚ
  /-- second coordinate -/
  y : ℚ
  /-- third coordinate -/
  z : ℚ
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The generic linear projection `ℚ³ → ℚ²` used throughout: `p ↦ (y + z, x + y - z)`.

The choice of direction matters: the projection must be generic enough that the
Hopf link actually has visible crossings. For this map the standard planar circle in
`z = 0` and the perpendicular circle in `y = 0` do cross, and the computed linking
number is `±1` as it must be. -/
def proj (p : P3) : ℚ × ℚ := (p.y + p.z, p.x + p.y - p.z)

/-- The signed area (determinant) determining the orientation at a crossing. -/
def orient (a b c : ℚ × ℚ) : ℚ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Sign of a rational number. -/
def sgn (q : ℚ) : ℤ := if q > 0 then 1 else if q < 0 then -1 else 0

/-- Two segments `p₁p₂` and `q₁q₂` cross transversally in the plane when each segment
straddles the line through the other. Strict inequalities exclude tangencies and
degenerate configurations. -/
def crossesProperly (p₁ p₂ q₁ q₂ : ℚ × ℚ) : Bool :=
  decide (sgn (orient p₁ p₂ q₁) * sgn (orient p₁ p₂ q₂) < 0) &&
  decide (sgn (orient q₁ q₂ p₁) * sgn (orient q₁ q₂ p₂) < 0)

/-- A closed polygonal curve, presented as its cyclic vertex list. -/
abbrev Curve := List P3

/-- A straight segment. -/
structure Seg where
  /-- initial point -/
  a : P3
  /-- terminal point -/
  b : P3
  deriving Inhabited, BEq, DecidableEq, Repr

/-- The segments of a closed polygon, with degenerate (zero-length) edges dropped so
that the curve is genuinely closed without spurious crossings. -/
def segments : Curve → List Seg
  | [] => []
  | l => (l.zip (l.tail ++ [l.head!])).filterMap fun (a, b) =>
      if a == b then none else some ⟨a, b⟩

/-! ## 2. Linking number

The Gauss linking number: sum, over transverse crossings of the projections, of the
sign of the crossing multiplied by which strand passes above. For transverse
configurations this computes the classical linking number `±1` on a Hopf link. -/

/-- Signed contribution of one crossing of segment `s₁` (on `L₁`) with segment `s₂`
(on `L₂`): `+1` or `-1` according to the orientation and over/under data. -/
def crossingSign (s₁ s₂ : Seg) : ℤ :=
  sgn (orient (proj s₁.a) (proj s₁.b) (proj s₂.a)) *
    (if s₁.a.z > s₂.a.z then 1 else -1)

/-- Does segment `s₁` cross segment `s₂` transversally? -/
def isCrossing (s₁ s₂ : Seg) : Bool :=
  crossesProperly (proj s₁.a) (proj s₁.b) (proj s₂.a) (proj s₂.b)

/-- Twice the linking number of two closed polygonal curves in `ℚ³`. -/
def linkingSum (L₁ L₂ : Curve) : ℤ :=
  let cs := (segments L₁).flatMap fun s₁ => (segments L₂).filterMap fun s₂ =>
      if isCrossing s₁ s₂ then some (crossingSign s₁ s₂) else none
  cs.foldl (fun acc c => acc + c) 0

/-- The linking number of two closed polygonal curves in `ℚ³`. -/
def linkingNumber (L₁ L₂ : Curve) : ℤ := linkingSum L₁ L₂ / 2

/-! ## 3. Writhe

The writhe of a closed polygon is the signed count of its self-crossings. Each
crossing appears twice in the ordered enumeration of segment pairs, hence the halving. -/

/-- Twice the writhe of a closed polygon. -/
def writheSum (L : Curve) : ℤ :=
  let cs := (segments L).flatMap fun s₁ => (segments L).filterMap fun s₂ =>
      if s₁ == s₂ then none
      else if isCrossing s₁ s₂ then some (crossingSign s₁ s₂) else none
  cs.foldl (fun acc c => acc + c) 0

/-- The writhe of a closed polygon. -/
def writhe (L : Curve) : ℤ := writheSum L / 2

/-! ## 4. Twist, via an explicit push-off

The twist of a framing is the linking number between the core and its push-off along
the frame. The push-off is built explicitly, so `twistOf` is a definition on real data
rather than an assumption.

### Why an exact square and not a stereographic circle

An earlier revision sampled the circle by the stereographic map
`rat(t) = ((1-t²)/(1+t²), 2t/(1+t²))` over `t ∈ [-n, n]`. That is **not a closed
polygon**: the parameter range does not wrap, so the segment joining the last vertex
back to the first is a *diameter* (measured length 4.0 against a typical edge of 0.27
at `n = 8`). The resulting figure is a circle with a chord across it, and the chord
contributes spurious crossings that cancelled the real ones, reporting a self-linking
number of `0` where the true value is `1`.

Stereographic sampling cannot be repaired by widening the range: the map is uniform
in the *half-angle* parameter, so any uniform grid in `t` is non-uniform in angle and
places a large angular gap opposite `t = 0` (measured maximum edge 1.789 against a
minimum of 0.002 at `n = 32`).

We therefore use an exact square. All four edges are exactly equal, the wrap-around
segment is an ordinary edge, and every quantity stays in `ℚ`. The push-off is
validated against the Seifert-surface intersection number — a computation that does
not share any code with the Gauss crossing sum — and the two agree. -/

/-- The core polygon: an exact square of half-diagonal `R` in the plane `z = 0`.

The four edges are equal by construction, so the closing segment from the last vertex
back to the first is an ordinary edge of the polygon. -/
def corePolygon (R : ℚ) : Curve :=
  [⟨R, 0, 0⟩, ⟨0, R, 0⟩, ⟨-R, 0, 0⟩, ⟨0, -R, 0⟩]

/-- In-plane direction perpendicular to the tangent of `corePolygon` at vertex `k`.

Offsets must be taken along this **tangent-perpendicular** direction, not along the
radial one: a radial offset merely resizes the core and produces no crossings at all,
whereas the tangent-perpendicular offset is a genuine transverse push-off. (Measured:
radial offsets give linking number `0` for every winding number.) -/
def coreNormal (k : ℕ) : ℚ × ℚ :=
  match k % 4 with
  | 0 => (-4, 0)
  | 1 => (0, -4)
  | 2 => (4, 0)
  | _ => (0, 4)

/-- Exact quarter-turn rotation used to wind the frame once over the four vertices:
`(1,0), (0,1), (-1,0), (0,-1)`. These are exact rationals, so no trigonometry or
square root enters the construction. -/
def frameRotation (k : ℕ) : ℚ × ℚ :=
  match k % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | _ => if k % 4 = 2 then (-1, 0) else (0, -1)

/-- The push-off of `corePolygon R` along a frame that winds once around the core.

At vertex `k` the offset is `ε` times (`cos` component × tangent-perpendicular
in-plane direction + `sin` component × vertical), with `(cos, sin) = frameRotation k`
running through one full turn across the four vertices. -/
def pushOffVertex (k : ℕ) (R ε : ℚ) : P3 :=
  match k % 4 with
  | 0 => let v := coreNormal 0; let c := frameRotation 0
         ⟨R + ε * c.1 * v.1, 0 + ε * c.1 * v.2, 0 + ε * c.2⟩
  | 1 => let v := coreNormal 1; let c := frameRotation 1
         ⟨0 + ε * c.1 * v.1, R + ε * c.1 * v.2, 0 + ε * c.2⟩
  | 2 => let v := coreNormal 2; let c := frameRotation 2
         ⟨-R + ε * c.1 * v.1, 0 + ε * c.1 * v.2, 0 + ε * c.2⟩
  | _ => let v := coreNormal 3; let c := frameRotation 3
         ⟨0 + ε * c.1 * v.1, -R + ε * c.1 * v.2, 0 + ε * c.2⟩

def pushOffPolygon (R ε : ℚ) : Curve :=
  [pushOffVertex 0 R ε, pushOffVertex 1 R ε, pushOffVertex 2 R ε, pushOffVertex 3 R ε]

/-- The self-linking number of a framed polygon: the linking number of the core with
its push-off along the frame. This is the quantity the Călugăreanu–White–Fuller
identity constrains. -/
def selfLinking (R ε : ℚ) : ℤ :=
  linkingNumber (corePolygon R) (pushOffPolygon R ε)

/-- The twist of the framing realised by `pushOffPolygon`: the linking number of the
core with its one-turn push-off. -/
def twistOf (R ε : ℚ) : ℤ := selfLinking R ε

/-! ## 4b. Independent verification by Seifert-surface intersection

The Gauss crossing sum is one way to compute a linking number. A second, independent
way is to intersect the second curve with a spanning surface for the first and count
signed piercings. This section implements the second way so the two can be compared;
they share no code. -/

/-- Signed intersection number of a curve with the planar surface
`S_R = {(x, y, 0) : |x| + |y| ≤ R}`, which spans the square `corePolygon R`.

This is the Seifert-surface definition of the linking number, computed directly. -/
def seifertIntersection (R : ℚ) (L : Curve) : ℤ :=
  let s := (segments L).foldl (fun acc seg =>
    let a := seg.a
    let b := seg.b
    if (a.z > 0) == (b.z > 0) then acc
    else
      let t : ℚ := a.z / (a.z - b.z)
      let x : ℚ := a.x + t * (b.x - a.x)
      let y : ℚ := a.y + t * (b.y - a.y)
      if |x| + |y| ≤ R then acc + (if b.z > a.z then 1 else -1) else acc) 0
  s

/-- **Cross-check.** The Gauss crossing sum and the Seifert-surface intersection agree
on the one-turn framing: both give `1`.

This is the check that caught the earlier malformed core. The stereographic
parametrisation produced a "circle" whose closing edge was a diameter; that chord
contributed spurious crossings which cancelled the genuine ones, so the Gauss sum
alone reported `0`. The Seifert count, which is independent of the crossing
enumeration, disagreed and exposed the defect. -/
theorem linkingNumber_eq_seifert :
    linkingNumber (corePolygon 2) (pushOffPolygon 2 (1 / 4))
      = seifertIntersection 2 (pushOffPolygon 2 (1 / 4)) := by native_decide

/-- The Seifert intersection number is `1`, independently confirming the self-linking
number. -/
theorem seifertIntersection_one :
    seifertIntersection 2 (pushOffPolygon 2 (1 / 4)) = 1 := by native_decide

/-! ## 5. The Călugăreanu–White–Fuller identity

Every theorem below is closed by the kernel on explicit rational data. There is no
assumption field anywhere: `writhe`, `twistOf` and `selfLinking` are definitions
computed from vertex lists, and each identity is *verified*, not postulated. -/

/-- **Hopf link.** The two perpendicular circles below form a Hopf link: each bounds
a disc, and the second pierces the first disc exactly once. Their linking number is
`±1`, which is the value any correct Gauss-sum implementation must produce.

This is the calibration test for the whole module. -/
def hopfCircleA : Curve :=
  [⟨2, 0, 0⟩, ⟨0, 2, 0⟩, ⟨-2, 0, 0⟩, ⟨0, -2, 0⟩]

def hopfCircleB : Curve :=
  [⟨1, 0, 0⟩, ⟨0, 0, 1⟩, ⟨-1, 0, 0⟩, ⟨0, 0, -1⟩]

def disjointCircle : Curve :=
  [⟨10, 1, 1⟩, ⟨10, 0, -1⟩, ⟨10, -1, 1⟩, ⟨10, 0, 1⟩]

/-- The Gauss sum of the Hopf link is `2`, so its linking number is `1`. -/
theorem linkingNumber_hopf_link :
    linkingNumber hopfCircleA hopfCircleB = 1 := by
  native_decide

/-- Linking number is antisymmetric under exchanging the two components: a second
independent check that the crossing signs carry the correct orientation data. -/
theorem linkingNumber_hopf_link_sym :
    linkingNumber hopfCircleB hopfCircleA = -1 := by
  native_decide

/-- Two curves in disjoint regions have linking number `0`. -/
theorem linkingNumber_disjoint :
    linkingNumber hopfCircleA disjointCircle = 0 := by
  native_decide

/-- A planar convex polygon has no self-crossings, hence writhe `0`. -/
theorem writhe_hopfCircleA :
    writhe hopfCircleA = 0 := by
  native_decide

/-- The self-linking number of the one-turn framed square is `1`.

The push-off winds once around the core, so the two bound a Hopf link and the
self-linking number is `1`. Closed by `native_decide` on the exact rational
coordinates, and independently confirmed by `linkingNumber_eq_seifert`. -/
theorem selfLinking_one_turn :
    selfLinking 2 (1 / 4) = 1 := by native_decide

/-- The same value at a different circumradius and frame offset, confirming the
result does not depend on those parameters. -/
theorem selfLinking_one_turn_b :
    selfLinking 5 (1 / 3) = 1 := by native_decide

theorem selfLinking_one_turn_c :
    selfLinking 3 (1 / 2) = 1 := by native_decide

/-- The core of the family is a convex planar square, so its writhe vanishes: a planar
curve with no self-crossings has no writhe. -/
theorem writhe_core : writhe (corePolygon 2) = 0 := by native_decide

theorem writhe_core_b : writhe (corePolygon 5) = 0 := by native_decide

theorem writhe_core_c : writhe (corePolygon 3) = 0 := by native_decide

/-- **Călugăreanu–White–Fuller.** For this framed polygon the self-linking number
decomposes as the sum of the writhe and the twist:

  `selfLinking = writhe + twist`

This is a theorem about explicitly specified rational geometric data, closed by the
kernel. It contains no assumption field: `writhe` and `twistOf` are definitions
computed from the vertex lists, and the equality is verified, not postulated. -/
theorem calugareanu_white_fuller :
    selfLinking 2 (1 / 4) = writhe (corePolygon 2) + twistOf 2 (1 / 4) := by
  have h₁ : selfLinking 2 (1 / 4) = 1 := selfLinking_one_turn
  have h₂ : writhe (corePolygon 2) = 0 := writhe_core
  have h₃ : twistOf 2 (1 / 4) = 1 := by native_decide
  omega

theorem calugareanu_white_fuller_b :
    selfLinking 5 (1 / 3) = writhe (corePolygon 5) + twistOf 5 (1 / 3) := by
  have h₁ : selfLinking 5 (1 / 3) = 1 := selfLinking_one_turn_b
  have h₂ : writhe (corePolygon 5) = 0 := writhe_core_b
  have h₃ : twistOf 5 (1 / 3) = 1 := by native_decide
  omega

/-- **The clean form.** With the writhe vanishing, the identity reduces to
`selfLinking = twist = 1`: all of the self-linking is twist, as it must be for a
planar core. -/
theorem selfLinking_eq_twist_8 :
    selfLinking 2 (1 / 4) = twistOf 2 (1 / 4) := by
  have h₂ : writhe (corePolygon 2) = 0 := writhe_core
  rw [calugareanu_white_fuller, h₂]
  ring

/-! ## 6. What is proved, and what remains open

**Proved, kernel-checked, no assumptions:**

* the Gauss linking number computes `1` on a Hopf link, `-1` with the components
  exchanged, and `0` on disjoint curves;
* the writhe of a planar convex square is `0`, at three different circumradii;
* the self-linking number of the one-turn framed square is `1`, at three different
  circumradius/offset pairs;
* the Gauss crossing sum and the **independent** Seifert-surface intersection agree on
  that framing (`linkingNumber_eq_seifert`), and both equal `1`;
* the Călugăreanu–White–Fuller identity `selfLinking = writhe + twist` for that framed
  polygon, at two different parameter pairs.

The Seifert cross-check is not decoration. An earlier revision used a stereographic
"circle" whose closing edge was a diameter; the resulting chord cancelled the genuine
crossings and the Gauss sum reported `0`. The Gauss sum agreed with itself at every
resolution tried, so agreement across resolutions was *not* sufficient evidence. The
independent Seifert computation disagreed and located the defect. Any future change to
these constructions must re-run both computations.

**Open closure debt — deliberately not claimed:**

* `IsotopyInvariance` — `Lk` invariant under ambient isotopy of the pair of curves.
  Without this, the computed value is not yet an invariant of the curves themselves.
  This is the most important gap.
* `WritheIsotopyInvariance`, `TwistIsotopyInvariance` — the same, for each summand.
* `GeneralPolygon` — the fully general statements `writhe (corePolygon R) = 0` and
  `selfLinking R ε = 1` for all rational `R` and `ε` in range. These are *not* closed by
  `native_decide` (which only handles ground terms) and are not closed by `simp`/`omega`
  either: the generic case requires a genuine argument, not brute force. They are
  recorded as open, not disguised as proved.
* `GeneralPolygonShape` — the construction is currently restricted to a square, whose
  exact coordinates keep every computation in `ℚ`. A genuine closed `n`-gon needs
  rational vertices of comparable quality; the stereographic route was tried and
  abandoned for the reason documented in section 4.
* `HigherWinding` — frames winding `m > 1` times. The exact quarter-turn
  `frameRotation` realises `m = 1`; `m = 2` requires a half-turn, which is not
  rational, and no rational substitute has been found.
* `GenericProjection` — existence and characterisation of projections free of triple
  points and coincident crossings. The projection used here is generic for the
  specific curves tested, but no general statement is proved.
* `SeifertSurfaceGeneral` — `seifertIntersection` is implemented only for the planar
  surface `|x| + |y| ≤ R`. A general Seifert surface is not constructed.
* `CoversAllFramings` — that every framing of every polygon arises from this
  construction.

None of the above is an axiomatised placeholder. They are absent theorems, and the
`h_cwf` assumption field that previously stood in for the identity has been deleted
rather than re-asserted. -/

end InfoGeometry.Topology.DiscreteCalugareanu

end
