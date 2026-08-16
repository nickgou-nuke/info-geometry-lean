import InfoGeometry.Core.SymmetricLie
import InfoGeometry.Canonical.TKKJordanPairData

/-!
# TKK symmetric-pair adapter

This file is a thin adapter between the existing involutive Lie-automorphism
owner and the existing abstract TKK grade owner.  It adds no Cartan projector
structure and no second five-grading implementation.

The grade-preservation predicate is kept explicit: the TKK data structure has
separate bundled instance fields, so a concrete realization must provide its
own compatibility theorem before a grade-level projector statement is made.
No Pin(5,5) action, root decomposition, Casimir, or Standard Model
identification is asserted here.
-/

namespace InfoGeometry.Canonical.Pin55TKKSymmetricPairBridge

open InfoGeometry.Core
open TKKJordanPairData

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- An involution preserves the formal TKK grades. -/
def PreservesFiveGrade (G : FiveGradedLieAlgebra ℝ)
    (θ : InvolutiveLieAut G.L) : Prop :=
  ∀ i (x : G.L), x ∈ G.grade i → θ.1 x ∈ G.grade i

/-- Opposite-grade involution on the five TKK grades. -/
def gradeNeg : TKKGrade → TKKGrade
  | TKKGrade.m2 => TKKGrade.p2
  | TKKGrade.m1 => TKKGrade.p1
  | TKKGrade.z0 => TKKGrade.z0
  | TKKGrade.p1 => TKKGrade.m1
  | TKKGrade.p2 => TKKGrade.m2

@[simp] theorem gradeNeg_gradeNeg (i : TKKGrade) :
    gradeNeg (gradeNeg i) = i := by
  cases i <;> rfl

@[simp] theorem gradeNeg_m2 : gradeNeg TKKGrade.m2 = TKKGrade.p2 := rfl
@[simp] theorem gradeNeg_m1 : gradeNeg TKKGrade.m1 = TKKGrade.p1 := rfl
@[simp] theorem gradeNeg_z0 : gradeNeg TKKGrade.z0 = TKKGrade.z0 := rfl
@[simp] theorem gradeNeg_p1 : gradeNeg TKKGrade.p1 = TKKGrade.m1 := rfl
@[simp] theorem gradeNeg_p2 : gradeNeg TKKGrade.p2 = TKKGrade.m2 := rfl

/-- Opposite-grade reversal commutes with the partial five-grade addition. -/
theorem gradeNeg_gradeAdd
    {i j k : TKKGrade}
    (hijk : gradeAdd i j = some k) :
    gradeAdd (gradeNeg i) (gradeNeg j) = some (gradeNeg k) := by
  cases i <;> cases j <;> cases k <;>
    simp [gradeAdd, gradeNeg, weight, ofWeight] at hijk ⊢

/-- Brackets outside the five-grade window remain outside after reversal. -/
theorem gradeNeg_gradeAdd_none
    {i j : TKKGrade}
    (hij : gradeAdd i j = none) :
    gradeAdd (gradeNeg i) (gradeNeg j) = none := by
  cases i <;> cases j <;>
    simp [gradeAdd, gradeNeg, weight, ofWeight] at hij ⊢

/-- A Lie involution reverses the five TKK grades. -/
def ReversesFiveGrade (G : FiveGradedLieAlgebra ℝ)
    (θ : InvolutiveLieAut G.L) : Prop :=
  ∀ i (x : G.L), x ∈ G.grade i → θ.1 x ∈ G.grade (gradeNeg i)

theorem reversesFiveGrade_apply (G : FiveGradedLieAlgebra ℝ)
    (θ : InvolutiveLieAut G.L)
    (hθ : ReversesFiveGrade G θ)
    (i : TKKGrade) {x : G.L} (hx : x ∈ G.grade i) :
    θ.1 x ∈ G.grade (gradeNeg i) :=
  hθ i x hx

/-! The Lie involution carries a homogeneous bracket output to the opposite
grade, without introducing a coordinate or matrix model. -/
theorem reversingFiveGrade_bracket_mem
    (G : FiveGradedLieAlgebra ℝ)
    (θ : InvolutiveLieAut G.L)
    (hθ : ReversesFiveGrade G θ)
    {i j k : TKKGrade}
    (hijk : gradeAdd i j = some k)
    {x y : G.L}
    (hx : x ∈ G.grade i)
    (hy : y ∈ G.grade j) :
    θ.1 ⁅x, y⁆ ∈ G.grade (gradeNeg k) := by
  exact hθ k ⁅x, y⁆ (bracket_grade_closed G hijk hx hy)

/-! The equivalent bracket-of-images form uses the native Lie equivalence law. -/
theorem reversingFiveGrade_bracket_of_images_mem
    (G : FiveGradedLieAlgebra ℝ)
    (θ : InvolutiveLieAut G.L)
    (hθ : ReversesFiveGrade G θ)
    {i j k : TKKGrade}
    (hijk : gradeAdd i j = some k)
    {x y : G.L}
    (hx : x ∈ G.grade i)
    (hy : y ∈ G.grade j) :
    ⁅θ.1 x, θ.1 y⁆ ∈ G.grade (gradeNeg k) := by
  rw [← θ.1.map_lie x y]
  exact reversingFiveGrade_bracket_mem G θ hθ hijk hx hy

theorem preservesFiveGrade_apply (G : FiveGradedLieAlgebra ℝ)
    (θ : InvolutiveLieAut G.L)
    (hθ : PreservesFiveGrade G θ)
    (i : TKKGrade) {x : G.L} (hx : x ∈ G.grade i) :
    θ.1 x ∈ G.grade i :=
  hθ i x hx

/-- The existing symmetric-Lie owner associated with an involution. -/
noncomputable def symmetricLie (θ : InvolutiveLieAut L) :
    SymmetricLieAlgebra L :=
  SymmetricLieAlgebra.ofInvolutiveLieAut θ

@[simp] theorem symmetricLie_theta_apply
    (θ : InvolutiveLieAut L) (x : L) :
    (symmetricLie θ).θ x = θ.1 x :=
  rfl

theorem cartan_decomposition (θ : InvolutiveLieAut L) (x : L) :
    x = (symmetricLie θ).P_plus x + (symmetricLie θ).P_minus x :=
  SymmetricLieAlgebra.cartan_decomposition (symmetricLie θ) x

theorem symmetric_pair_properties (θ : InvolutiveLieAut L) :
    (∀ {x y}, x ∈ (symmetricLie θ).evenLieSubalgebra →
      y ∈ (symmetricLie θ).evenLieSubalgebra →
      ⁅x, y⁆ ∈ (symmetricLie θ).evenLieSubalgebra) ∧
    (∀ {x y}, x ∈ (symmetricLie θ).evenLieSubalgebra →
      y ∈ (symmetricLie θ).oddSubmodule →
      ⁅x, y⁆ ∈ (symmetricLie θ).oddSubmodule) ∧
    (∀ {x y}, x ∈ (symmetricLie θ).oddSubmodule →
      y ∈ (symmetricLie θ).oddSubmodule →
      ⁅x, y⁆ ∈ (symmetricLie θ).evenLieSubalgebra) :=
  SymmetricLieAlgebra.symmetric_pair_properties (symmetricLie θ)

theorem bracket_grade_closed_readout
    (G : FiveGradedLieAlgebra ℝ)
    {i j k : TKKGrade} (hijk : gradeAdd i j = some k)
    {x y : G.L} (hx : x ∈ G.grade i) (hy : y ∈ G.grade j) :
    ⁅x, y⁆ ∈ G.grade k :=
  TKKJordanPairData.bracket_grade_closed G hijk hx hy

end InfoGeometry.Canonical.Pin55TKKSymmetricPairBridge
