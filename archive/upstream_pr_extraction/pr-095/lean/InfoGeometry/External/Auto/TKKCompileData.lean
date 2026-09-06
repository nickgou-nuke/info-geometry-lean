import Mathlib.Tactic
import InfoGeometry.Canonical.TKKJordanPairData

/-!
# Native TKK compilation bridge

This compatibility module preserves the archived compilation idea while
reusing the canonical TKK owner.  The aliases below are not new proof
packets: `JordanPairData` already carries the Jordan-pair identities and
`TKKLieData` already carries the native Lie/module structure and grade
closure laws.
-/

noncomputable section

namespace TKKCompileData

open TKKJordanPairData

abbrev TKKGrade := TKKJordanPairData.TKKGrade

namespace TKKGrade

abbrev weight : TKKGrade → ℤ := TKKJordanPairData.weight
abbrev add? : TKKGrade → TKKGrade → Option TKKGrade := TKKJordanPairData.gradeAdd

end TKKGrade

abbrev JordanPairData (R : Type*) [CommRing R] := TKKJordanPairData.JordanPair R
abbrev TKKLieData (R : Type*) [CommRing R] := TKKJordanPairData.FiveGradedLieAlgebra R

theorem tkk_bracket_mem
    {R : Type*} [CommRing R] (G : TKKLieData R)
    {i j k : TKKGrade} (hgrade : TKKGrade.add? i j = some k)
    {x y : G.L} (hx : x ∈ G.grade i) (hy : y ∈ G.grade j) :
    ⁅x, y⁆ ∈ G.grade k :=
  TKKJordanPairData.bracket_grade_closed G hgrade hx hy

theorem tkk_bracket_zero_of_outside
    {R : Type*} [CommRing R] (G : TKKLieData R)
    {i j : TKKGrade} (hgrade : TKKGrade.add? i j = none)
    {x y : G.L} (hx : x ∈ G.grade i) (hy : y ∈ G.grade j) :
    ⁅x, y⁆ = 0 :=
  TKKJordanPairData.bracket_grade_outside_zero G hgrade hx hy

abbrev SpacetimeGeometryData :=
  Σ tangent : Type, tangent → tangent → Real

namespace SpacetimeGeometryData

def tangent (data : SpacetimeGeometryData) : Type := data.1
def metric (data : SpacetimeGeometryData) : tangent data → tangent data → Real := data.2

end SpacetimeGeometryData

structure ChiralToSpacetimeCompileData
    (R : Type*) [CommRing R] where
  jordanPair : JordanPairData R
  tkk : TKKLieData R
  spacetime : SpacetimeGeometryData

def compileChiralToSpacetimeData
    {R : Type*} [CommRing R] (C : ChiralToSpacetimeCompileData R) :
    SpacetimeGeometryData :=
  C.spacetime

end TKKCompileData
