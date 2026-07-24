import InfoGeometry.Canonical.FierzKleinFoundation

/-!
# Projective line geometry in Pluecker coordinates

This file extracts the coordinate `P^3` line-geometry fragment used in
Hestenes--Ziegler's projective-geometric Clifford-algebra presentation.

The scope is intentionally narrow:

* points are real four-vectors;
* projective lines are decomposable bivectors, detected by the Klein form;
* point-line incidence is the coordinate equation `p ∧ L = 0`.

No general blade calculus, regressive product, or pseudoscalar-duality API is
introduced here.
-/

noncomputable section

namespace InfoGeometry.Erlangen.ProjectiveLineGeometry

open InfoGeometry.Canonical.FierzKleinFoundation

/-- Points in projective `P^3`, represented before quotienting by nonzero scale. -/
abbrev Point4 := Vec4

/-- Bivector coordinates for projective lines or general screws in `P^3`. -/
abbrev Line4 := Bivector4

/-- Trivector coordinates in `Λ³ ℝ⁴`. -/
@[ext]
structure Trivector4 where
  p012 : ℝ
  p013 : ℝ
  p023 : ℝ
  p123 : ℝ

/-- The zero trivector. -/
def zeroTrivector4 : Trivector4 where
  p012 := 0
  p013 := 0
  p023 := 0
  p123 := 0

/-- Exterior product of a point and a bivector in coordinates. -/
def wedgePointLine (p : Point4) (L : Line4) : Trivector4 where
  p012 := p I4.t * L.p12 - p I4.x * L.p02 + p I4.y * L.p01
  p013 := p I4.t * L.p13 - p I4.x * L.p03 + p I4.z * L.p01
  p023 := p I4.t * L.p23 - p I4.y * L.p03 + p I4.z * L.p02
  p123 := p I4.x * L.p23 - p I4.y * L.p13 + p I4.z * L.p12

/-- Point-line incidence: `p` lies on `L` exactly when `p ∧ L = 0`. -/
def PointOnLine (p : Point4) (L : Line4) : Prop :=
  wedgePointLine p L = zeroTrivector4

/-- The line through two representative points. -/
def lineThrough (p q : Point4) : Line4 :=
  wedgeVec4 p q

/-- A bivector is a projective line when it lies on the Klein quadric. -/
def IsProjectiveLine (L : Line4) : Prop :=
  IsOnKleinQuadric L

/-- General bivectors in `Λ² ℝ⁴`, interpreted as screws in classical line geometry. -/
abbrev Screw4 := Bivector4

/-- A screw degenerates to a line exactly when its Pluecker/Klein form vanishes. -/
def IsLineScrew (S : Screw4) : Prop :=
  IsOnKleinQuadric S

/-- The first endpoint lies on the generated line. -/
theorem pointOnLine_left (p q : Point4) :
    PointOnLine p (lineThrough p q) := by
  unfold PointOnLine lineThrough wedgePointLine wedgeVec4 zeroTrivector4
  ext <;> ring

/-- The second endpoint lies on the generated line. -/
theorem pointOnLine_right (p q : Point4) :
    PointOnLine q (lineThrough p q) := by
  unfold PointOnLine lineThrough wedgePointLine wedgeVec4 zeroTrivector4
  ext <;> ring

/-- Every generated line is decomposable, hence is a projective line. -/
theorem lineThrough_isProjectiveLine (p q : Point4) :
    IsProjectiveLine (lineThrough p q) := by
  unfold IsProjectiveLine lineThrough
  exact wedgeVec4_on_klein p q

/-- Generated projective lines are line-screws in the `P^3` line-geometry sense. -/
theorem lineThrough_isLineScrew (p q : Point4) :
    IsLineScrew (lineThrough p q) := by
  exact lineThrough_isProjectiveLine p q

end InfoGeometry.Erlangen.ProjectiveLineGeometry
