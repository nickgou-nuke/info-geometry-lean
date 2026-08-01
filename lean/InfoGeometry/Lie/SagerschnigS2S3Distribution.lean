import Mathlib.Tactic
import InfoGeometry.Projective.SplitOctonions.SplitOctonionsTraceIncidence

/-!
# Sagerschnig's explicit `S² × S³` distribution formula

This file packages the explicit coordinate formula from Sagerschnig's 2006
paper on split octonions and the homogeneous `(2,3,5)` model.

It records the exact pointwise distribution on the product sphere
`S² × S³` in coordinates `(x, (α, y))` with `x ∈ ℝ³`, `α ∈ ℝ`, and
`y ∈ ℝ³`.
-/

namespace InfoGeometry.Lie.SagerschnigS2S3Distribution

open InfoGeometry.Projective.SplitOctonions

/-- The coordinate cross product on `ℝ³`. -/
def cross {𝕜 : Type} [CommRing 𝕜] (u v : Vec3 𝕜) : Vec3 𝕜 :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

/-- Scalar multiplication on the coordinate `ℝ³` carrier. -/
def smulVec3 (r : ℝ) (v : Vec3 ℝ) : Vec3 ℝ :=
  (r * v.1, r * v.2.1, r * v.2.2)

@[simp] theorem dot_cross_cyclic (a b c : Vec3 ℝ) :
    Vec3.dot (cross a b) c = Vec3.dot a (cross b c) := by
  unfold Vec3.dot cross
  ring

@[simp] theorem dot_cross_zero_sum (a b c : Vec3 ℝ) :
    Vec3.dot (cross a b) c + Vec3.dot b (cross a c) = 0 := by
  unfold Vec3.dot cross
  ring

/-- The raw Sagerschnig coordinate carrier for `S² × S³`. -/
abbrev S2xS3Coordinates := Vec3 ℝ × (ℝ × Vec3 ℝ)

/-- The defining equations for a point of `S² × S³`. -/
def S2xS3PointPredicate (p : S2xS3Coordinates) : Prop :=
  Vec3.dot p.1 p.1 = 1 ∧ p.2.1 ^ 2 + Vec3.dot p.2.2 p.2.2 = 1

/-- A point of `S² × S³`, natively represented as a subtype of coordinates. -/
abbrev S2xS3Point := {p : S2xS3Coordinates // S2xS3PointPredicate p}

namespace S2xS3Point

abbrev x (p : S2xS3Point) : Vec3 ℝ := p.1.1
abbrev alpha (p : S2xS3Point) : ℝ := p.1.2.1
abbrev y (p : S2xS3Point) : Vec3 ℝ := p.1.2.2

theorem hx (p : S2xS3Point) : Vec3.dot p.x p.x = 1 := p.2.1

theorem hy (p : S2xS3Point) : p.alpha ^ 2 + Vec3.dot p.y p.y = 1 := p.2.2

end S2xS3Point

/-- Tangent vectors in coordinates `(v, (β, w))`. -/
abbrev S2xS3Tangent := Vec3 ℝ × (ℝ × Vec3 ℝ)

/--
Sagerschnig's explicit distribution on `S² × S³`.

At a point `(x,(α,y))`, the distribution is

`{ (v,(β,w)) : ⟨x,v⟩ = 0, β = ⟨v × y, x⟩,
   w = ⟨v,y⟩ x + α (v × x) - ⟨y,x⟩ v }`.
-/
def sagerschnigDistribution (p : S2xS3Point) : Set S2xS3Tangent :=
  {q |
    Vec3.dot p.x q.1 = 0 ∧
      q.2.1 = Vec3.dot (cross q.1 p.y) p.x ∧
      q.2.2 = smulVec3 (Vec3.dot q.1 p.y) p.x + smulVec3 p.alpha (cross q.1 p.x) -
        smulVec3 (Vec3.dot p.y p.x) q.1}

/-- Pointwise readback of Sagerschnig's explicit `S² × S³` distribution formula. -/
theorem sagerschnigDistribution_formula (p : S2xS3Point) (q : S2xS3Tangent) :
    q ∈ sagerschnigDistribution p ↔
      Vec3.dot p.x q.1 = 0 ∧
        q.2.1 = Vec3.dot (cross q.1 p.y) p.x ∧
        q.2.2 = smulVec3 (Vec3.dot q.1 p.y) p.x + smulVec3 p.alpha (cross q.1 p.x) -
          smulVec3 (Vec3.dot p.y p.x) q.1 := by
  rfl

/-- The first tangent constraint is built into the distribution definition. -/
theorem sagerschnigDistribution_first_tangent_constraint
    (p : S2xS3Point) (q : S2xS3Tangent)
    (hq : q ∈ sagerschnigDistribution p) :
    Vec3.dot p.x q.1 = 0 := by
  simpa [sagerschnigDistribution] using hq.1

/-- The second coordinate is the scalar triple-product term. -/
theorem sagerschnigDistribution_beta_formula
    (p : S2xS3Point) (q : S2xS3Tangent)
    (hq : q ∈ sagerschnigDistribution p) :
    q.2.1 = Vec3.dot (cross q.1 p.y) p.x := by
  simpa [sagerschnigDistribution] using hq.2.1

/-- The third coordinate is the explicit vector field from Sagerschnig's corollary. -/
theorem sagerschnigDistribution_w_formula
    (p : S2xS3Point) (q : S2xS3Tangent)
    (hq : q ∈ sagerschnigDistribution p) :
    q.2.2 = smulVec3 (Vec3.dot q.1 p.y) p.x + smulVec3 p.alpha (cross q.1 p.x) -
      smulVec3 (Vec3.dot p.y p.x) q.1 := by
  simpa [sagerschnigDistribution] using hq.2.2

end InfoGeometry.Lie.SagerschnigS2S3Distribution
