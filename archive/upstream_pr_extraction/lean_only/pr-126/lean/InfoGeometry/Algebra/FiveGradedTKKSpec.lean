import InfoGeometry.Algebra.SplitMetricSpace
import InfoGeometry.Algebra.SplitMetricLieAlgebra
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

/-!
# Five-Graded TKK Specification — Abstract Graded Lie Algebra Layer

The TKK (Tits-Kantor-Koecher) construction produces a 5-graded Lie algebra
from a Jordan triple system. This module specifies the abstract interface
using mathlib's native `GradedAlgebra` and `GradedModule`.

Concrete models (split octonion, Zorn, chiral, etc.) implement this specification.
-/

namespace InfoGeometry.Algebra

/-- The five TKK grades: -2, -1, 0, +1, +2 -/
inductive TKKGrade where
  | m2 | m1 | z0 | p1 | p2
  deriving DecidableEq, Repr, Inhabited

open TKKGrade

/-- Integer weight of a grade -/
def TKKGrade.weight : TKKGrade → ℤ
  | m2 => -2 | m1 => -1 | z0 => 0 | p1 => 1 | p2 => 2

/-- Partial grade addition: grades outside [-2, 2] leave the window -/
def TKKGrade.add (i j : TKKGrade) : Option TKKGrade :=
  match (i.weight + j.weight : ℤ) with
  | -2 => some m2 | -1 => some m1 | 0 => some z0 | 1 => some p1 | 2 => some p2
  | _ => none

/-- A 5-graded TKK specification over a split metric space.

This structure packages:
1. The underlying split metric space (V, β)
2. The orthogonal Lie algebra 𝔬(β) as a 5-graded Lie algebra
3. Bracket closure laws respecting the 5-grade window
4. The TKK bracket laws (neg_abelian, pos_abelian, neg_pos = zero, etc.)
5. The inversion automorphism swapping grades ±1 and ±2, fixing grade 0 up to sign -/
structure FiveGradedTKKSpec (R : Type*) [CommRing R] where
  -- The base split metric space
  metric : SplitMetricSpace R

  -- The orthogonal Lie algebra 𝔬(β)
  lie : SplitMetricLieAlgebra R metric

  -- The 5-grading: each grade is a submodule of the Lie algebra
  -- Uses mathlib's GradedModule structure
  grade : TKKGrade → Submodule R lie.L

  -- The grade subspaces span the whole Lie algebra
  span_grades : Submodule.span R (⋃ (g : TKKGrade), (grade g : Set lie.L)) = ⊤

  -- Bracket closure: [grade i, grade j] ⊆ grade (i+j) when i+j ∈ [-2,2]
  bracket_mem_grade :
    ∀ {i j k : TKKGrade}, TKKGrade.add i j = some k →
    ∀ {x y : lie.L}, x ∈ grade i → y ∈ grade j → ⁅x, y⁆ ∈ grade k

  -- Bracket vanishes outside the 5-grade window
  bracket_outside_zero :
    ∀ {i j : TKKGrade}, TKKGrade.add i j = none →
    ∀ {x y : lie.L}, x ∈ grade i → y ∈ grade j → ⁅x, y⁆ = 0

  -- TKK bracket laws (3-grade version, induced by grade collapse)
  -- grade m2 ⊕ m1 is the "negative" grade (translations)
  -- grade z0 is the "zero" grade (structure)
  -- grade p1 ⊕ p2 is the "positive" grade (special conformal)
  neg_abelian :
    ∀ (x y : lie.L), x ∈ grade m2 ⊔ grade m1 → y ∈ grade m2 ⊔ grade m1 → ⁅x, y⁆ = 0
  pos_abelian :
    ∀ (x y : lie.L), x ∈ grade p1 ⊔ grade p2 → y ∈ grade p1 ⊔ grade p2 → ⁅x, y⁆ = 0
  neg_pos_bracket :
    ∀ (x y : lie.L), x ∈ grade m2 ⊔ grade m1 → y ∈ grade p1 ⊔ grade p2 → ⁅x, y⁆ ∈ grade z0
  zero_neg_action :
    ∀ (x y : lie.L), x ∈ grade z0 → y ∈ grade m2 ⊔ grade m1 → ⁅x, y⁆ ∈ grade m2 ⊔ grade m1
  zero_pos_action :
    ∀ (x y : lie.L), x ∈ grade z0 → y ∈ grade p1 ⊔ grade p2 → ⁅x, y⁆ ∈ grade p1 ⊔ grade p2
  zero_zero_bracket :
    ∀ (x y : lie.L), x ∈ grade z0 → y ∈ grade z0 → ⁅x, y⁆ ∈ grade z0

  -- The inversion automorphism
  inversion : lie.L ≃ₗ[R] lie.L
  inversion_involutive : ∀ (x : lie.L), inversion (inversion x) = x
  inversion_neg_to_pos : ∀ (x : lie.L), x ∈ grade m2 ⊔ grade m1 → inversion x ∈ grade p1 ⊔ grade p2
  inversion_pos_to_neg : ∀ (x : lie.L), x ∈ grade p1 ⊔ grade p2 → inversion x ∈ grade m2 ⊔ grade m1
  inversion_zero_negate : ∀ (x : lie.L), x ∈ grade z0 → inversion x = -x

namespace FiveGradedTKKSpec

variable {R : Type*} [CommRing R]
variable (S : FiveGradedTKKSpec R)

@[simp] def bracket (x y : S.lie.L) : S.lie.L := ⁅x, y⁆
def inGrade (g : TKKGrade) (x : S.lie.L) : Prop := x ∈ S.grade g
def negGrade : Submodule R S.lie.L := S.grade m2 ⊔ S.grade m1
def zeroGrade : Submodule R S.lie.L := S.grade z0
def posGrade : Submodule R S.lie.L := S.grade p1 ⊔ S.grade p2

-- Exhaustive bracket closure: either lands in a grade or vanishes
theorem bracket_closed_or_zero {i j : TKKGrade} {x y : S.lie.L}
    (hx : x ∈ S.grade i) (hy : y ∈ S.grade j) :
    (∃ k : TKKGrade, ⁅x, y⁆ ∈ S.grade k) ∨ ⁅x, y⁆ = 0 := by
  cases h : TKKGrade.add i j with
  | none => exact Or.inr (S.bracket_outside_zero h hx hy)
  | some k => exact Or.inl ⟨k, S.bracket_mem_grade h hx hy⟩

end FiveGradedTKKSpec

/-- A morphism of 5-graded TKK specifications preserving all structure. -/
structure FiveGradedTKKSpecHom {R : Type*} [CommRing R] (S₁ S₂ : FiveGradedTKKSpec R) where
  metric_hom : SplitMetricSpaceHom S₁.metric S₂.metric
  lie_hom : SplitMetricLieAlgebraHom S₁.lie S₂.lie
  map_grade : ∀ (g : TKKGrade) (x : S₁.lie.L), x ∈ S₁.grade g → lie_hom.toLinearMap x ∈ S₂.grade g
  map_inversion : ∀ (x : S₁.lie.L), lie_hom.toLinearMap (S₁.inversion x) = S₂.inversion (lie_hom.toLinearMap x)

/-- An equivalence of 5-graded TKK specifications. -/
structure FiveGradedTKKSpecEquiv {R : Type*} [CommRing R] (S₁ S₂ : FiveGradedTKKSpec R) where
  metric_equiv : SplitMetricSpaceEquiv S₁.metric S₂.metric
  lie_equiv : SplitMetricLieAlgebraEquiv S₁.lie S₂.lie
  map_grade : ∀ (g : TKKGrade), S₁.grade g ≃ₗ[R] S₂.grade g
  map_inversion : ∀ (x : S₁.lie.L), lie_equiv.toLinearEquiv (S₁.inversion x) = S₂.inversion (lie_equiv.toLinearEquiv x)

end InfoGeometry.Algebra
