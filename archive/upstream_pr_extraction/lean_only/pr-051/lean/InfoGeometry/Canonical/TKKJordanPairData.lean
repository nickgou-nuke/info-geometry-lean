import Mathlib.Tactic
import Mathlib.Algebra.Lie.Basic

/-!
# Abstract TKK/Jordan-pair data

This recovered owner keeps the theorem-honest, self-contained part of the
archived `ZornAuto/TKKJordanPairData` lane:

* the five formal TKK grades;
* grade arithmetic inside the `[-2,2]` window;
* abstract Jordan-pair data;
* abstract five-graded Lie-algebra data.

The archived file also tried to bundle a concrete finite chiral/Krein seed from
an unavailable external owner. That import is intentionally not promoted here
until the missing owner is restored independently.
-/

noncomputable section

namespace TKKJordanPairData

/-- The five formal TKK grades. -/
inductive TKKGrade where
  | m2 | m1 | z0 | p1 | p2
  deriving DecidableEq, Repr, Inhabited

open TKKGrade

/-- Integer weight of a TKK grade. -/
def weight : TKKGrade → ℤ
  | m2 => -2
  | m1 => -1
  | z0 => 0
  | p1 => 1
  | p2 => 2

/-- Partial inverse from weights to the five TKK grades. -/
def ofWeight : ℤ → Option TKKGrade
  | -2 => some m2
  | -1 => some m1
  | 0 => some z0
  | 1 => some p1
  | 2 => some p2
  | _ => none

/-- Partial grade addition: brackets outside `[-2,2]` leave the five-grade window. -/
def gradeAdd (i j : TKKGrade) : Option TKKGrade := ofWeight (weight i + weight j)

/-- Grade zero acts internally on every grade. -/
theorem gradeAdd_z0_left (i : TKKGrade) : gradeAdd z0 i = some i := by
  cases i <;> rfl

/-- Grade zero acts internally on every grade. -/
theorem gradeAdd_z0_right (i : TKKGrade) : gradeAdd i z0 = some i := by
  cases i <;> rfl

/-- The two extremal positive/negative brackets leave the five-grade window. -/
theorem gradeAdd_p2_p1_none : gradeAdd p2 p1 = none := rfl

theorem gradeAdd_m2_m1_none : gradeAdd m2 m1 = none := rfl

/-- The main conformal pairing returns to grade zero. -/
theorem gradeAdd_m1_p1 : gradeAdd m1 p1 = some z0 := rfl

theorem gradeAdd_m2_p2 : gradeAdd m2 p2 = some z0 := rfl

/-- Abstract Jordan pair data over `R`. -/
structure JordanPair (R : Type*) [CommRing R] where
  Vplus : Type*
  Vminus : Type*
  [plus_add : AddCommGroup Vplus]
  [minus_add : AddCommGroup Vminus]
  [plus_module : Module R Vplus]
  [minus_module : Module R Vminus]
  triplePlus : Vplus → Vminus → Vplus → Vplus
  tripleMinus : Vminus → Vplus → Vminus → Vminus
  /-- Outer symmetry of the positive Jordan-pair product. -/
  triplePlus_outer :
    ∀ x y z, triplePlus x y z = triplePlus z y x
  /-- Outer symmetry of the negative Jordan-pair product. -/
  tripleMinus_outer :
    ∀ x y z, tripleMinus x y z = tripleMinus z y x
  /-- Fundamental Jordan-pair identity in the positive component. -/
  triplePlus_fundamental :
    ∀ (x u w : Vplus) (y v : Vminus),
      triplePlus x y (triplePlus u v w) -
          triplePlus u v (triplePlus x y w) =
        triplePlus (triplePlus x y u) v w -
          triplePlus u (tripleMinus y x v) w
  /-- Fundamental Jordan-pair identity in the negative component. -/
  tripleMinus_fundamental :
    ∀ (x u w : Vminus) (y v : Vplus),
      tripleMinus x y (tripleMinus u v w) -
          tripleMinus u v (tripleMinus x y w) =
        tripleMinus (tripleMinus x y u) v w -
          tripleMinus u (triplePlus y x v) w

attribute [instance] JordanPair.plus_add JordanPair.minus_add
attribute [instance] JordanPair.plus_module JordanPair.minus_module

namespace JordanPair

variable {R : Type*} [CommRing R] (J : JordanPair R)

/-- Consolidated readback of the four defining Jordan-pair identities. -/
theorem jordanPairIdentities :
    (∀ x y z, J.triplePlus x y z = J.triplePlus z y x) ∧
      (∀ x y z, J.tripleMinus x y z = J.tripleMinus z y x) ∧
      (∀ (x u w : J.Vplus) (y v : J.Vminus),
        J.triplePlus x y (J.triplePlus u v w) -
            J.triplePlus u v (J.triplePlus x y w) =
          J.triplePlus (J.triplePlus x y u) v w -
            J.triplePlus u (J.tripleMinus y x v) w) ∧
      (∀ (x u w : J.Vminus) (y v : J.Vplus),
        J.tripleMinus x y (J.tripleMinus u v w) -
            J.tripleMinus u v (J.tripleMinus x y w) =
          J.tripleMinus (J.tripleMinus x y u) v w -
            J.tripleMinus u (J.triplePlus y x v) w) :=
  ⟨J.triplePlus_outer, J.tripleMinus_outer,
    J.triplePlus_fundamental, J.tripleMinus_fundamental⟩

end JordanPair

/-- A five-graded Lie-algebra interface indexed by `TKKGrade`. -/
structure FiveGradedLieAlgebra (R : Type*) [CommRing R] where
  L : Type*
  [lie_ring : LieRing L]
  [add_comm_group : AddCommGroup L]
  [module : Module R L]
  [lie_algebra : LieAlgebra R L]
  grade : TKKGrade → Submodule R L
  bracket_mem_some : ∀ {i j k : TKKGrade}, gradeAdd i j = some k →
    ∀ {x y : L}, x ∈ grade i → y ∈ grade j → ⁅x, y⁆ ∈ grade k
  bracket_eq_zero_none : ∀ {i j : TKKGrade}, gradeAdd i j = none →
    ∀ {x y : L}, x ∈ grade i → y ∈ grade j → ⁅x, y⁆ = 0

attribute [instance] FiveGradedLieAlgebra.lie_ring FiveGradedLieAlgebra.add_comm_group
attribute [instance] FiveGradedLieAlgebra.module FiveGradedLieAlgebra.lie_algebra

/-- Reusable bracket closure theorem for any concrete TKK implementation. -/
theorem bracket_grade_closed {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    {i j k : TKKGrade} (hijk : gradeAdd i j = some k)
    {x y : G.L} (hx : x ∈ G.grade i) (hy : y ∈ G.grade j) :
    ⁅x, y⁆ ∈ G.grade k :=
  G.bracket_mem_some hijk hx hy

/-- Reusable theorem: brackets beyond the five-grade window vanish. -/
theorem bracket_grade_outside_zero {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    {i j : TKKGrade} (hij : gradeAdd i j = none)
    {x y : G.L} (hx : x ∈ G.grade i) (hy : y ∈ G.grade j) :
    ⁅x, y⁆ = 0 :=
  G.bracket_eq_zero_none hij hx hy

/-!
`gradeAdd` is a partial operation because the five-grade window is finite.
The following theorem is the usable exhaustive closure statement: a bracket
of homogeneous elements either lands in one of the five graded submodules or
vanishes when the formal grade sum leaves the window.
-/
theorem bracket_grade_closed_or_zero
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    {i j : TKKGrade} {x y : G.L}
    (hx : x ∈ G.grade i) (hy : y ∈ G.grade j) :
    (∃ k : TKKGrade, ⁅x, y⁆ ∈ G.grade k) ∨ ⁅x, y⁆ = 0 := by
  cases h : gradeAdd i j with
  | none =>
      exact Or.inr (bracket_grade_outside_zero G h hx hy)
  | some k =>
      exact Or.inl ⟨k, bracket_grade_closed G h hx hy⟩

theorem gradeAdd_none_iff_natAbs_weight_sum_gt_two
    (i j : TKKGrade) :
    gradeAdd i j = none ↔
      2 < Int.natAbs (weight i + weight j) := by
  cases i <;> cases j <;> decide

theorem gradeAdd_some_weight_eq_sum
    {i j k : TKKGrade}
    (hijk : gradeAdd i j = some k) :
    weight k = weight i + weight j := by
  cases i <;> cases j <;> cases k <;>
    simp [gradeAdd, ofWeight, weight] at hijk ⊢

theorem bracket_grade_outside_window_zero
    {R : Type*} [CommRing R] (G : FiveGradedLieAlgebra R)
    {i j : TKKGrade}
    (hij : 2 < Int.natAbs (weight i + weight j))
    {x y : G.L} (hx : x ∈ G.grade i) (hy : y ∈ G.grade j) :
    ⁅x, y⁆ = 0 := by
  exact bracket_grade_outside_zero G
    ((gradeAdd_none_iff_natAbs_weight_sum_gt_two i j).2 hij) hx hy

/-- Core definitional readout preserved from the archived lane. -/
theorem tkk_jordan_pair_data_synthesis :
    gradeAdd z0 p1 = some p1 ∧
    gradeAdd m1 p1 = some z0 ∧
    gradeAdd p2 p1 = none := by
  constructor
  · rfl
  constructor <;> rfl

end TKKJordanPairData
