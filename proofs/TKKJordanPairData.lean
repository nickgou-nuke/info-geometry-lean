import Mathlib
import proofs.SpectralSquashCayleyDKT

/-!
# Abstract TKK/Jordan-pair data

This file defines a small formal interface for Jordan-pair and five-graded
TKK-style Lie-algebra data, together with the finite chiral Krein seed imported
from `SpectralSquashCayleyDKT`.
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

/-- Partial grade addition: brackets outside `[-2,2]` are forced to the zero
component in a 5-graded Lie algebra. -/
def gradeAdd (i j : TKKGrade) : Option TKKGrade := ofWeight (weight i + weight j)

/-- Grade zero acts internally on every grade. -/
theorem gradeAdd_z0_left (i : TKKGrade) : gradeAdd z0 i = some i := by
  cases i <;> rfl

/-- Grade zero acts internally on every grade. -/
theorem gradeAdd_z0_right (i : TKKGrade) : gradeAdd i z0 = some i := by
  cases i <;> rfl

/-- The two extremal positive/negative brackets leave the 5-grade window. -/
theorem gradeAdd_p2_p1_none : gradeAdd p2 p1 = none := rfl

theorem gradeAdd_m2_m1_none : gradeAdd m2 m1 = none := rfl

/-- The main conformal pairing returns to grade zero. -/
theorem gradeAdd_m1_p1 : gradeAdd m1 p1 = some z0 := rfl

theorem gradeAdd_m2_p2 : gradeAdd m2 p2 = some z0 := rfl

/-- Abstract Jordan pair data over `R`.

The carrier types, additive/module structures, two triple products, and the
chosen Jordan-pair identity proposition are fields of the structure. -/
structure JordanPair (R : Type*) [CommRing R] where
  Vplus : Type*
  Vminus : Type*
  [plus_add : AddCommGroup Vplus]
  [minus_add : AddCommGroup Vminus]
  [plus_module : Module R Vplus]
  [minus_module : Module R Vminus]
  triplePlus : Vplus → Vminus → Vplus → Vplus
  tripleMinus : Vminus → Vplus → Vminus → Vminus
  jordanPairIdentities : Prop

attribute [instance] JordanPair.plus_add JordanPair.minus_add
attribute [instance] JordanPair.plus_module JordanPair.minus_module

/-- A five-graded Lie-algebra interface indexed by `TKKGrade`.

This structure contains only fields: the carrier Lie algebra, its five
submodules, bracket closure for grade sums inside `[-2, 2]`, and bracket
vanishing for grade sums outside that range. -/
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

/-- The local finite chiral datum already proved in `SpectralSquashCayleyDKT`:
`η=N₊-N₋`, `η²=1`, and self-adjointness. -/
structure ChiralKreinSeed where
  endogenousSignature : SpectralSquashCayleyDKT.eta =
    SpectralSquashCayleyDKT.Nplus - SpectralSquashCayleyDKT.Nminus
  signatureInvolution : SpectralSquashCayleyDKT.eta * SpectralSquashCayleyDKT.eta = 1
  signatureSelfAdjoint : star SpectralSquashCayleyDKT.eta = SpectralSquashCayleyDKT.eta

/-- The concrete finite seed is available without postulating a background
metric. -/
def finiteChiralKreinSeed : ChiralKreinSeed where
  endogenousSignature := SpectralSquashCayleyDKT.eta_eq_projection_difference
  signatureInvolution := SpectralSquashCayleyDKT.eta_sq
  signatureSelfAdjoint := SpectralSquashCayleyDKT.eta_selfadjoint

/-- A record bundling a Jordan pair, five-graded Lie-algebra data, the finite
chiral Krein seed, and four named propositions for downstream geometry
interfaces. -/
structure TKKCompileData (R : Type*) [CommRing R] where
  pair : JordanPair R
  tkk : FiveGradedLieAlgebra R
  seed : ChiralKreinSeed
  gradeZeroReceivesEta : Prop
  realForm_su22_or_so24 : Prop
  tangentMinkowskiProjection13 : Prop
  freudenthalRealFormSelection : Prop

/-- Definitional equalities for the finite chiral Krein seed and selected
grade-addition cases. -/
theorem tkk_jordan_pair_data_synthesis :
    finiteChiralKreinSeed.endogenousSignature =
      SpectralSquashCayleyDKT.eta_eq_projection_difference ∧
    finiteChiralKreinSeed.signatureInvolution = SpectralSquashCayleyDKT.eta_sq ∧
    gradeAdd z0 p1 = some p1 ∧
    gradeAdd m1 p1 = some z0 ∧
    gradeAdd p2 p1 = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end TKKJordanPairData
