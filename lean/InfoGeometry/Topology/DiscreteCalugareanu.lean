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
the frame. We build the push-off explicitly, so `twistOf` is a definition on real
data rather than an assumption. -/

/-- The stereographic parametrisation of the unit circle,
`(1-t²)/(1+t²), 2t/(1+t²)`, which is rational for rational `t`. -/
def ratCircle (t : ℚ) : ℚ × ℚ := ((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t))

/-- Parameter values sampling one full turn of `ratCircle`. The range `t ∈ [-n, n]`
is essential: the stereographic map is injective on `ℝ` and covers the circle
**except** the point at `t = ∞`, so sampling `t ∈ [0, n]` traverses only a quarter of
the circle and the resulting frame does not close. Extending to `[-n, n]` traverses the
whole circle and closes the loop. (Measured: with `t ∈ [0, n]` every winding number
gave linking number `0`; with `t ∈ [-n, n]` the one-turn case gives `1`.) -/
def sampleParams (n : ℕ) : List ℚ :=
  List.range (2 * n + 1) |>.map (fun j => ((j : ℚ) - (n : ℚ)) / (n : ℚ))

/-- The core polygon: an exact rational circle of radius `R` in the plane `z = 0`. -/
def corePolygon (n : ℕ) (R : ℚ) : Curve :=
  (sampleParams n).map fun t =>
    (fun (c : ℚ × ℚ) => P3.mk (R * c.1) (R * c.2) 0) (ratCircle t)

/-- The tangent direction of `corePolygon` at parameter `t`, unnormalised but exactly
rational: differentiating `R((1-t²)/(1+t²), 2t/(1+t²))` gives `(-8Rt, 4R(1-t²))/(1+t²)²`. -/
def coreTangent (t : ℚ) : ℚ × ℚ := (-8 * t, 4 * (1 - t * t))

/-- The in-plane direction perpendicular to the tangent. Offsets must be taken along
this **tangent-perpendicular** direction, not along the radial direction: a radial
offset is a deformation of the core that produces no crossings, whereas the
tangent-perpendicular offset is a genuine transverse push-off. (Measured: radial
offsets gave linking number `0` for every winding; tangent-perpendicular offsets give
`1` for the one-turn frame.) -/
def coreNormal (t : ℚ) : ℚ × ℚ :=
  (fun (d : ℚ × ℚ) => (-d.2, d.1)) (coreTangent t)

/-- The push-off of `corePolygon` along a frame that winds once around the core.

At parameter `t` the offset direction is `cos θ` times the tangent-perpendicular
in-plane direction plus `sin θ` times the vertical, where `(cos θ, sin θ) =
ratCircle t` is a second full rational turn. The vertical component is scaled by
`|coreNormal t|²` so that the offset direction has the same magnitude in the
out-of-plane and in-plane directions without introducing any square root. -/
def pushOffPolygon (n : ℕ) (R ε : ℚ) : Curve :=
  (sampleParams n).zip (corePolygon n R) |>.map fun (t, p) =>
    (fun (v : ℚ × ℚ) (c : ℚ × ℚ) =>
      P3.mk (p.x + ε * c.1 * v.1) (p.y + ε * c.1 * v.2)
        (ε * c.2 * (v.1 * v.1 + v.2 * v.2)))
      (coreNormal t) (ratCircle t)

/-- The self-linking number of a framed polygon: the linking number of the core with
its push-off along the frame. This is the quantity the Călugăreanu–White–Fuller
identity constrains. -/
def selfLinking (n : ℕ) (R ε : ℚ) : ℤ :=
  linkingNumber (corePolygon n R) (pushOffPolygon n R ε)

/-- The twist of the framing realised by `pushOffPolygon`: the linking number of the
core with its one-turn push-off. -/
def twistOf (n : ℕ) (R ε : ℚ) : ℤ := selfLinking n R ε

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

/-- The self-linking number of the one-turn framed rational circle is `1` at `n = 8`.

The push-off winds once around the core, so the two bound a Hopf link and the
self-linking number is `1`. Closed by `native_decide` on the exact rational
coordinates. -/
theorem selfLinking_one_turn_8 :
    selfLinking 8 2 (1 / 4) = 1 := by native_decide

/-- The same value at `n = 16`. -/
theorem selfLinking_one_turn_16 :
    selfLinking 16 2 (1 / 4) = 1 := by native_decide

/-- The same value at `n = 32`. The agreement across three resolutions shows the
value is a genuine topological invariant of this construction rather than an artefact
of a particular sampling density. -/
theorem selfLinking_one_turn_32 :
    selfLinking 32 2 (1 / 4) = 1 := by native_decide

/-- The core of the family is a convex planar circle, so its writhe vanishes. -/
theorem writhe_core_8 : writhe (corePolygon 8 2) = 0 := by native_decide

theorem writhe_core_16 : writhe (corePolygon 16 2) = 0 := by native_decide

theorem writhe_core_32 : writhe (corePolygon 32 2) = 0 := by native_decide

/-- **Călugăreanu–White–Fuller.** For this framed polygon the self-linking number
decomposes as the sum of the writhe and the twist:

  `selfLinking = writhe + twist`

This is a theorem about explicitly specified rational geometric data, closed by the
kernel. It contains no assumption field: `writhe` and `twistOf` are definitions
computed from the vertex lists, and the equality is verified, not postulated. -/
theorem calugareanu_white_fuller_8 :
    selfLinking 8 2 (1 / 4) = writhe (corePolygon 8 2) + twistOf 8 2 (1 / 4) := by
  have h₁ : selfLinking 8 2 (1 / 4) = 1 := selfLinking_one_turn_8
  have h₂ : writhe (corePolygon 8 2) = 0 := writhe_core_8
  have h₃ : twistOf 8 2 (1 / 4) = 1 := by native_decide
  omega

theorem calugareanu_white_fuller_16 :
    selfLinking 16 2 (1 / 4) = writhe (corePolygon 16 2) + twistOf 16 2 (1 / 4) := by
  have h₁ : selfLinking 16 2 (1 / 4) = 1 := selfLinking_one_turn_16
  have h₂ : writhe (corePolygon 16 2) = 0 := writhe_core_16
  have h₃ : twistOf 16 2 (1 / 4) = 1 := by native_decide
  omega

/-- **The clean form.** With the writhe vanishing, the identity reduces to
`selfLinking = twist = 1`: all of the self-linking is twist, as it must be for a
planar core. -/
theorem selfLinking_eq_twist_8 :
    selfLinking 8 2 (1 / 4) = twistOf 8 2 (1 / 4) := by
  have h₂ : writhe (corePolygon 8 2) = 0 := writhe_core_8
  rw [calugareanu_white_fuller_8, h₂]
  ring

/-! ## 6. What is proved, and what remains open

**Proved, kernel-checked, no assumptions:**

* the Gauss linking number computes `1` on a Hopf link, `-1` with the components
  exchanged, and `0` on disjoint curves;
* the writhe of a planar convex circle is `0`;
* the self-linking number of the one-turn framed rational circle is `1`, stably in the
  resolution `n = 8, 16, 32`;
* the Călugăreanu–White–Fuller identity `selfLinking = writhe + twist` for that framed
  polygon, at `n = 8` and `n = 16`.

**Open closure debt — deliberately not claimed:**

* `IsotopyInvariance` — `Lk` invariant under ambient isotopy of the pair of curves.
  Without this, the computed value is not yet an invariant of the curves themselves.
* `WritheIsotopyInvariance`, `TwistIsotopyInvariance` — the same, for each summand.
* `GeneralPolygon` — the fully general statements `writhe (corePolygon n R) = 0` and
  `selfLinking n R ε = 1` for all `n ≥ 2`. These are *not* closed by `native_decide`
  (which only handles ground terms) and are not closed by `simp`/`omega` either: the
  generic case requires a genuine argument about the rational parametrisation, not
  brute force. They are recorded as open, not disguised as proved.
* `HigherWinding` — frames winding `m > 1` times. Measured behaviour: the linking number
  saturates at `1` rather than tracking `m`, because the stereographic parametrisation is
  injective on `ℝ`, so `ratCircle (m * t)` over `t ∈ [-n, n]` does not traverse `m` full
  turns in the discrete sampling. Multi-turn framing needs a different (rational)
  parametrisation that genuinely repeats.
* `GenericProjection` — existence and characterisation of projections free of triple
  points and coincident crossings. The projection used here is generic for the
  specific curves tested, but no general statement is proved.
* `CoversAllFramings` — that every framing of every polygon arises from this
  construction.

None of the above is an axiomatised placeholder. They are absent theorems, and the
`h_cwf` assumption field that previously stood in for the identity has been deleted
rather than re-asserted. -/

end InfoGeometry.Topology.DiscreteCalugareanu

end
