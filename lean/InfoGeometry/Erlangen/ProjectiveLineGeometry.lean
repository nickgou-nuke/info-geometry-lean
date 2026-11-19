/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FierzKleinFoundation
import InfoGeometry.Canonical.KleinBivectorLinear
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

/-- Every projective bivector in four dimensions is a sum of two line blades.

This is the real six-coordinate `Λ² ℝ⁴` statement used in classical screw
geometry: the mixed coordinates are one blade through the chosen `t`-axis,
and the remaining three spatial coordinates form a blade in the three-space.
The sum need not itself be a line; its Klein value can be nonzero. -/
theorem everyBivector4_is_sum_of_two_lines (S : Screw4) :
    ∃ a b c d : Point4, S = lineThrough a b + lineThrough c d := by
  let e₀ : Point4 := fun i => if i = I4.t then 1 else 0
  let m : Point4 := fun i =>
    if i = I4.t then 0 else if i = I4.x then S.p01
      else if i = I4.y then S.p02 else S.p03
  by_cases h12 : S.p12 ≠ 0
  · let u : Point4 := fun i =>
      if i = I4.t then 0 else if i = I4.x then 1
        else if i = I4.y then 0 else -S.p23 / S.p12
    let v : Point4 := fun i =>
      if i = I4.t then 0 else if i = I4.x then 0
        else if i = I4.y then S.p12 else S.p13
    refine ⟨e₀, m, u, v, ?_⟩
    apply bivector4CoordinatesAddEquiv.injective
    rw [bivector4CoordinatesAddEquiv.map_add]
    ext i
    fin_cases i <;> simp [bivector4CoordinatesAddEquiv, bivector4Coordinates,
      lineThrough, e₀, m, u, v, wedgeVec4]
      <;> field_simp [h12] <;> ring_nf
  · by_cases h13 : S.p13 ≠ 0
    · let u : Point4 := fun i =>
        if i = I4.t then 0 else if i = I4.x then 1
          else if i = I4.y then S.p23 / S.p13 else 0
      let v : Point4 := fun i =>
        if i = I4.t then 0 else if i = I4.x then 0
          else if i = I4.y then 0 else S.p13
      have hp12 : S.p12 = 0 := by simpa using h12
      refine ⟨e₀, m, u, v, ?_⟩
      apply bivector4CoordinatesAddEquiv.injective
      rw [bivector4CoordinatesAddEquiv.map_add]
      ext i
      fin_cases i <;> simp [bivector4CoordinatesAddEquiv, bivector4Coordinates,
        lineThrough, e₀, m, u, v, wedgeVec4, hp12]
        <;> field_simp [h13] <;> ring_nf
    · let u : Point4 := fun i =>
        if i = I4.t then 0 else if i = I4.x then 0
          else if i = I4.y then 1 else 0
      let v : Point4 := fun i =>
        if i = I4.t then 0 else if i = I4.x then 0
          else if i = I4.y then 0 else S.p23
      have hp12 : S.p12 = 0 := by simpa using h12
      have hp13 : S.p13 = 0 := by simpa using h13
      refine ⟨e₀, m, u, v, ?_⟩
      apply bivector4CoordinatesAddEquiv.injective
      rw [bivector4CoordinatesAddEquiv.map_add]
      ext i
      fin_cases i <;> simp [bivector4CoordinatesAddEquiv, bivector4Coordinates,
        lineThrough, e₀, m, u, v, wedgeVec4, hp12, hp13]
        <;> ring_nf

/-- A sum of two lines can be a genuine screw rather than another line. The
coordinates `p01 = p23 = 1` give Klein value `1`, so the distinction between
the linear bivector carrier and its decomposable Klein locus is strict. -/
theorem sum_of_two_lines_can_be_nondecomposable :
    ∃ a b c d : Point4,
      ¬ IsProjectiveLine (lineThrough a b + lineThrough c d) := by
  let S : Screw4 := ⟨1, 0, 0, 0, 0, 1⟩
  obtain ⟨a, b, c, d, h⟩ := everyBivector4_is_sum_of_two_lines S
  refine ⟨a, b, c, d, ?_⟩
  rw [← h]
  norm_num [IsProjectiveLine, IsOnKleinQuadric, kleinForm, S]

end InfoGeometry.Erlangen.ProjectiveLineGeometry
