import Mathlib.Tactic

/-!
# TKK compile data

A finite interface for the next layer:

`JordanPairData -> TKKLieData -> SpacetimeGeometryData`.

This file does not assert a concrete `su(2,2)` realization.  It records finite
data for a Tits-Kantor-Koecher compilation:
outer symmetry of the Jordan pair, five-grade bracket closure, vanishing outside
the grade range, and the macroscopic spacetime metric data.
-/

noncomputable section

namespace TKKCompileData

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The five TKK grades. -/
inductive TKKGrade where
  | m2 | m1 | z0 | p1 | p2
  deriving DecidableEq, Repr

namespace TKKGrade

/-- Integer weight of a TKK grade. -/
def weight : TKKGrade -> Int
  | .m2 => -2
  | .m1 => -1
  | .z0 => 0
  | .p1 => 1
  | .p2 => 2

/-- Partial grade addition.  Values outside `[-2,2]` are sent to `none`,
encoding the zero grade subspace. -/
def add? (a b : TKKGrade) : Option TKKGrade :=
  match a.weight + b.weight with
  | -2 => some .m2
  | -1 => some .m1
  | 0 => some .z0
  | 1 => some .p1
  | 2 => some .p2
  | _ => none

theorem add?_weight {a b c : TKKGrade} (h : add? a b = some c) :
    c.weight = a.weight + b.weight := by
  cases a <;> cases b <;> cases c <;> simp [add?, weight] at h ⊢ <;> norm_num

end TKKGrade

/-- A Jordan pair datum supplies the two grade-one spaces and the triple
products needed by the universal TKK construction. -/
structure JordanPairData (R : Type*) [CommRing R] where
  Vplus : Type*
  Vminus : Type*
  triplePlus : Vplus -> Vminus -> Vplus -> Vplus
  tripleMinus : Vminus -> Vplus -> Vminus -> Vminus
  outerSymmetryPlus : forall x y z, triplePlus x y z = triplePlus z y x
  outerSymmetryMinus : forall x y z, tripleMinus x y z = tripleMinus z y x

/-- A five-graded TKK Lie datum with an abstract carrier. -/
structure TKKLieData (R : Type*) [CommRing R] [Zero R] where
  carrier : Type*
  zero : carrier
  bracket : carrier -> carrier -> carrier
  gradeSubspace : TKKGrade -> Set carrier
  bracket_mem : forall {i j k : TKKGrade} {x y : carrier},
    x ∈ gradeSubspace i ->
    y ∈ gradeSubspace j ->
    TKKGrade.add? i j = some k ->
    bracket x y ∈ gradeSubspace k
  bracket_zero : forall {i j : TKKGrade} {x y : carrier},
    x ∈ gradeSubspace i ->
    y ∈ gradeSubspace j ->
    TKKGrade.add? i j = none ->
    bracket x y = zero

/-- The graded bracket closure theorem is the data projection. -/
theorem tkk_bracket_mem
    {R : Type*} [CommRing R] [Zero R] (G : TKKLieData R)
    {i j k : TKKGrade} {x y : G.carrier}
    (hx : x ∈ G.gradeSubspace i) (hy : y ∈ G.gradeSubspace j)
    (hgrade : TKKGrade.add? i j = some k) :
    G.bracket x y ∈ G.gradeSubspace k := by
  exact G.bracket_mem hx hy hgrade

/-- Brackets whose grade sum leaves `[-2,2]` vanish in the five-graded model. -/
theorem tkk_bracket_zero_of_outside
    {R : Type*} [CommRing R] [Zero R] (G : TKKLieData R)
    {i j : TKKGrade} {x y : G.carrier}
    (hx : x ∈ G.gradeSubspace i) (hy : y ∈ G.gradeSubspace j)
    (hgrade : TKKGrade.add? i j = none) :
    G.bracket x y = G.zero := by
  exact G.bracket_zero hx hy hgrade

/-- The resulting macroscopic spacetime geometry. -/
structure SpacetimeGeometryData where
  tangent : Type*
  metric : tangent -> tangent -> Real

/-- The finite compilation target: a Jordan pair, a five-graded TKK datum, and
the resulting spacetime geometry datum. -/
structure ChiralToSpacetimeCompileData (R : Type*) [CommRing R] [Zero R] where
  jordanPair : JordanPairData R
  tkk : TKKLieData R
  spacetime : SpacetimeGeometryData

/-- A constructor-level compile projection returning the recorded spacetime
geometry datum. -/
def compileChiralToSpacetimeData
    {R : Type*} [CommRing R] [Zero R] (C : ChiralToSpacetimeCompileData R) :
    SpacetimeGeometryData :=
  C.spacetime

end TKKCompileData
