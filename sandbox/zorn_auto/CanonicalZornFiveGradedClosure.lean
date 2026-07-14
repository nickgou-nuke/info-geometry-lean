import CanonicalZornProjectiveTKKBridge
import TKKJordanPairData

/-!
# A concrete five-graded conformal closure for canonical Zorn coordinates

The existing Zorn/TKK bridges route named elements to grade labels.  This file
constructs an actual `FiveGradedLieAlgebra ℂ`.  Its carrier is the matrix Lie
algebra on a block decomposition

`ℂ ⊕ ℂ⁸ ⊕ ℂ`,

with block weights `-1, 0, 1`.  A matrix entry has grade equal to its row
weight minus its column weight.  Hence the commutator has grades
`-2,-1,0,1,2`, and brackets outside this window vanish.

The canonical complex Zorn carrier embeds injectively into both grade `+1`
and grade `-1`.  This is a concrete algebraic closure; no identification with
a particular simple real Lie group is asserted here.
-/

noncomputable section

namespace CanonicalZornFiveGradedClosure

open TKKJordanPairData
open TKKJordanPairData.TKKGrade
open SplitOctonionBraidSU3

/-- Indices for the conformal block decomposition `1 ⊕ 8 ⊕ 1`. -/
inductive ConformalIndex where
  | minus
  | middle (i : Fin 8)
  | plus
  deriving DecidableEq, Fintype

/-- Block weight of a conformal matrix index. -/
def indexWeight : ConformalIndex → ℤ
  | .minus => -1
  | .middle _ => 0
  | .plus => 1

abbrev ConformalMatrix := Matrix ConformalIndex ConformalIndex ℂ

/-- Matrices supported on entries of a fixed weight difference. -/
def conformalGrade (g : TKKGrade) : Submodule ℂ ConformalMatrix where
  carrier := {A | ∀ r c, indexWeight r - indexWeight c ≠ weight g → A r c = 0}
  zero_mem' := by
    intro r c _
    rfl
  add_mem' := by
    intro A B hA hB r c hrc
    simp [hA r c hrc, hB r c hrc]
  smul_mem' := by
    intro a A hA r c hrc
    simp [hA r c hrc]

theorem mem_conformalGrade_iff (A : ConformalMatrix) (g : TKKGrade) :
    A ∈ conformalGrade g ↔
      ∀ r c, indexWeight r - indexWeight c ≠ weight g → A r c = 0 :=
  Iff.rfl

theorem gradeAdd_weight {i j k : TKKGrade} (h : gradeAdd i j = some k) :
    weight k = weight i + weight j := by
  cases i <;> cases j <;> cases k <;>
    simp [gradeAdd, ofWeight, weight] at h ⊢

theorem gradeAdd_none_index_impossible {i j : TKKGrade}
    (h : gradeAdd i j = none) (r c : ConformalIndex) :
    indexWeight r - indexWeight c ≠ weight i + weight j := by
  cases i <;> cases j <;> cases r <;> cases c <;>
    simp [gradeAdd, ofWeight, weight, indexWeight] at h ⊢

private theorem product_entry_zero_of_grade_sum_ne
    {i j : TKKGrade} {A B : ConformalMatrix}
    (hA : A ∈ conformalGrade i) (hB : B ∈ conformalGrade j)
    (r c : ConformalIndex)
    (hrc : indexWeight r - indexWeight c ≠ weight i + weight j) :
    (A * B) r c = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hAm : indexWeight r - indexWeight m = weight i
  · have hBm : indexWeight m - indexWeight c ≠ weight j := by
      intro h
      apply hrc
      calc
        indexWeight r - indexWeight c =
            (indexWeight r - indexWeight m) +
              (indexWeight m - indexWeight c) := by ring
        _ = weight i + weight j := by rw [hAm, h]
    rw [hB m c hBm]
    simp
  · rw [hA r m hAm]
    simp

private theorem bracket_mem_conformalGrade
    {i j k : TKKGrade} (hijk : gradeAdd i j = some k)
    {A B : ConformalMatrix}
    (hA : A ∈ conformalGrade i) (hB : B ∈ conformalGrade j) :
    ⁅A, B⁆ ∈ conformalGrade k := by
  rw [mem_conformalGrade_iff]
  intro r c hrc
  have hw := gradeAdd_weight hijk
  have hsum : indexWeight r - indexWeight c ≠ weight i + weight j := by
    intro h
    apply hrc
    rw [hw, h]
  change (A * B - B * A) r c = 0
  rw [Matrix.sub_apply,
    product_entry_zero_of_grade_sum_ne hA hB r c hsum]
  have hsum' : indexWeight r - indexWeight c ≠ weight j + weight i := by
    simpa [add_comm] using hsum
  rw [product_entry_zero_of_grade_sum_ne hB hA r c hsum']
  simp

private theorem bracket_zero_outside
    {i j : TKKGrade} (hij : gradeAdd i j = none)
    {A B : ConformalMatrix}
    (hA : A ∈ conformalGrade i) (hB : B ∈ conformalGrade j) :
    ⁅A, B⁆ = 0 := by
  ext r c
  have hsum := gradeAdd_none_index_impossible hij r c
  change (A * B - B * A) r c = 0
  rw [Matrix.sub_apply,
    product_entry_zero_of_grade_sum_ne hA hB r c hsum]
  have hji : gradeAdd j i = none := by
    cases i <;> cases j <;> simp [gradeAdd, ofWeight, weight] at hij ⊢
  have hsum' := gradeAdd_none_index_impossible hji r c
  rw [product_entry_zero_of_grade_sum_ne hB hA r c hsum']
  simp

/-- The concrete `|2|`-graded matrix Lie algebra on `1 ⊕ 8 ⊕ 1`. -/
def canonicalFiveGradedLieAlgebra : FiveGradedLieAlgebra ℂ where
  L := ConformalMatrix
  grade := conformalGrade
  bracket_mem_some := fun hijk _ _ hA hB =>
    bracket_mem_conformalGrade hijk hA hB
  bracket_eq_zero_none := fun hij _ _ hA hB =>
    bracket_zero_outside hij hA hB

/-! ## Canonical Zorn embeddings in grades `+1` and `-1` -/

/-- Eight canonical complex coordinates of a Zorn element. -/
def zornCoordinates (X : Zorn) : Fin 8 → ℂ :=
  ![X.a, X.u 0, X.u 1, X.u 2, X.v 0, X.v 1, X.v 2, X.b]

theorem zornCoordinates_injective : Function.Injective zornCoordinates := by
  intro X Y h
  apply zorn_ext
  · exact congrFun h 0
  · funext i
    fin_cases i
    · exact congrFun h 1
    · exact congrFun h 2
    · exact congrFun h 3
  · funext i
    fin_cases i
    · exact congrFun h 4
    · exact congrFun h 5
    · exact congrFun h 6
  · exact congrFun h 7

/-- Translation-type embedding of a Zorn vector in grade `+1`. -/
def zornPositive (X : Zorn) : ConformalMatrix :=
  fun r c => match r, c with
    | .plus, .middle i => zornCoordinates X i
    | _, _ => 0

/-- Special-conformal-type embedding of a Zorn vector in grade `-1`. -/
def zornNegative (X : Zorn) : ConformalMatrix :=
  fun r c => match r, c with
    | .middle i, .plus => zornCoordinates X i
    | _, _ => 0

/-- The second grade `+1` block, from the negative endpoint into the middle. -/
def zornPositiveSource (X : Zorn) : ConformalMatrix :=
  fun r c => match r, c with
    | .middle i, .minus => zornCoordinates X i
    | _, _ => 0

/-- The second grade `-1` block, from the middle into the negative endpoint. -/
def zornNegativeTarget (X : Zorn) : ConformalMatrix :=
  fun r c => match r, c with
    | .minus, .middle i => zornCoordinates X i
    | _, _ => 0

theorem zornPositive_mem (X : Zorn) :
    zornPositive X ∈ conformalGrade p1 := by
  intro r c h
  cases r <;> cases c <;> simp [zornPositive, indexWeight, weight] at h ⊢

theorem zornNegative_mem (X : Zorn) :
    zornNegative X ∈ conformalGrade m1 := by
  intro r c h
  cases r <;> cases c <;> simp [zornNegative, indexWeight, weight] at h ⊢

theorem zornPositiveSource_mem (X : Zorn) :
    zornPositiveSource X ∈ conformalGrade p1 := by
  intro r c h
  cases r <;> cases c <;>
    simp [zornPositiveSource, indexWeight, weight] at h ⊢

theorem zornNegativeTarget_mem (X : Zorn) :
    zornNegativeTarget X ∈ conformalGrade m1 := by
  intro r c h
  cases r <;> cases c <;>
    simp [zornNegativeTarget, indexWeight, weight] at h ⊢

theorem zornPositive_injective : Function.Injective zornPositive := by
  intro X Y h
  apply zornCoordinates_injective
  funext i
  exact congrFun (congrFun h .plus) (.middle i)

theorem zornNegative_injective : Function.Injective zornNegative := by
  intro X Y h
  apply zornCoordinates_injective
  funext i
  exact congrFun (congrFun h (.middle i)) .plus

theorem zornPositiveSource_injective : Function.Injective zornPositiveSource := by
  intro X Y h
  apply zornCoordinates_injective
  funext i
  exact congrFun (congrFun h (.middle i)) .minus

theorem zornNegativeTarget_injective : Function.Injective zornNegativeTarget := by
  intro X Y h
  apply zornCoordinates_injective
  funext i
  exact congrFun (congrFun h .minus) (.middle i)

/-- A concrete generator of the extremal positive grade. -/
def zornCoordinateZero : Zorn :=
  { a := 1, u := fun _ => 0, v := fun _ => 0, b := 0 }

/-- A concrete generator of the extremal positive grade. -/
def gradeTwoGenerator : ConformalMatrix :=
  ⁅zornPositive zornCoordinateZero, zornPositiveSource zornCoordinateZero⁆

/-- A concrete generator of the extremal negative grade. -/
def gradeMinusTwoGenerator : ConformalMatrix :=
  ⁅zornNegativeTarget zornCoordinateZero, zornNegative zornCoordinateZero⁆

theorem gradeTwoGenerator_mem : gradeTwoGenerator ∈ conformalGrade p2 := by
  exact bracket_grade_closed canonicalFiveGradedLieAlgebra (by rfl)
    (zornPositive_mem zornCoordinateZero)
    (zornPositiveSource_mem zornCoordinateZero)

theorem gradeMinusTwoGenerator_mem :
    gradeMinusTwoGenerator ∈ conformalGrade m2 := by
  exact bracket_grade_closed canonicalFiveGradedLieAlgebra (by rfl)
    (zornNegativeTarget_mem zornCoordinateZero)
    (zornNegative_mem zornCoordinateZero)

theorem gradeTwoGenerator_entry :
    gradeTwoGenerator .plus .minus = 1 := by
  change ((zornPositive zornCoordinateZero *
      zornPositiveSource zornCoordinateZero) -
    (zornPositiveSource zornCoordinateZero *
      zornPositive zornCoordinateZero)) .plus .minus = 1
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  have hsum :
      (∑ m : ConformalIndex,
        zornPositive zornCoordinateZero .plus m *
          zornPositiveSource zornCoordinateZero m .minus) = 1 := by
    classical
    rw [Fintype.sum_eq_single (ConformalIndex.middle 0)]
    · simp [zornPositive, zornPositiveSource, zornCoordinates,
        zornCoordinateZero]
    · intro m hm
      cases m
      · simp [zornPositive, zornPositiveSource]
      · rename_i i
        fin_cases i <;>
          simp_all [zornPositive, zornPositiveSource, zornCoordinates,
            zornCoordinateZero]
      · simp [zornPositive, zornPositiveSource]
  rw [hsum]
  simp [zornPositive, zornPositiveSource]

theorem gradeMinusTwoGenerator_entry :
    gradeMinusTwoGenerator .minus .plus = 1 := by
  change ((zornNegativeTarget zornCoordinateZero *
      zornNegative zornCoordinateZero) -
    (zornNegative zornCoordinateZero *
      zornNegativeTarget zornCoordinateZero)) .minus .plus = 1
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  have hsum :
      (∑ m : ConformalIndex,
        zornNegativeTarget zornCoordinateZero .minus m *
          zornNegative zornCoordinateZero m .plus) = 1 := by
    classical
    rw [Fintype.sum_eq_single (ConformalIndex.middle 0)]
    · simp [zornNegative, zornNegativeTarget, zornCoordinates,
        zornCoordinateZero]
    · intro m hm
      cases m
      · simp [zornNegative, zornNegativeTarget]
      · rename_i i
        fin_cases i <;>
          simp_all [zornNegative, zornNegativeTarget, zornCoordinates,
            zornCoordinateZero]
      · simp [zornNegative, zornNegativeTarget]
  rw [hsum]
  simp [zornNegative, zornNegativeTarget]

theorem gradeTwoGenerator_ne_zero : gradeTwoGenerator ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h ConformalIndex.plus) ConformalIndex.minus
  rw [gradeTwoGenerator_entry] at hentry
  simp at hentry

theorem gradeMinusTwoGenerator_ne_zero : gradeMinusTwoGenerator ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h ConformalIndex.minus) ConformalIndex.plus
  rw [gradeMinusTwoGenerator_entry] at hentry
  simp at hentry

/-- The mixed Zorn bracket closes in grade zero. -/
theorem zorn_mixed_bracket_mem_grade_zero (X Y : Zorn) :
    ⁅zornNegative X, zornPositive Y⁆ ∈ conformalGrade z0 := by
  exact bracket_grade_closed canonicalFiveGradedLieAlgebra gradeAdd_m1_p1
    (zornNegative_mem X) (zornPositive_mem Y)

/-- The concrete closure simultaneously realizes the five grade window and
injects both canonical Zorn lanes into the corresponding odd grades. -/
theorem canonical_zorn_five_grade_closure (X Y : Zorn) :
    zornPositive X ∈ conformalGrade p1 ∧
    zornNegative Y ∈ conformalGrade m1 ∧
    ⁅zornNegative Y, zornPositive X⁆ ∈ conformalGrade z0 ∧
    gradeTwoGenerator ∈ conformalGrade p2 ∧
    gradeMinusTwoGenerator ∈ conformalGrade m2 := by
  exact ⟨zornPositive_mem X, zornNegative_mem Y,
    zorn_mixed_bracket_mem_grade_zero Y X,
    gradeTwoGenerator_mem, gradeMinusTwoGenerator_mem⟩

/-! ## Triality on the conformal closure -/

/-- Relabel old Zorn coordinates into their new locations under triality. -/
def trialityCoordinateEquiv : Fin 8 ≃ Fin 8 where
  toFun := fun i => ![0, 3, 1, 2, 6, 4, 5, 7] i
  invFun := fun i => ![0, 2, 3, 1, 5, 6, 4, 7] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Triality fixes the two conformal endpoints and permutes the middle Zorn
coordinates. -/
def conformalIndexTriality : ConformalIndex ≃ ConformalIndex where
  toFun
    | .minus => .minus
    | .middle i => .middle (trialityCoordinateEquiv i)
    | .plus => .plus
  invFun
    | .minus => .minus
    | .middle i => .middle (trialityCoordinateEquiv.symm i)
    | .plus => .plus
  left_inv i := by cases i <;> simp
  right_inv i := by cases i <;> simp

@[simp] theorem indexWeight_conformalIndexTriality (i : ConformalIndex) :
    indexWeight (conformalIndexTriality i) = indexWeight i := by
  cases i <;> rfl

@[simp] theorem indexWeight_conformalIndexTriality_symm (i : ConformalIndex) :
    indexWeight (conformalIndexTriality.symm i) = indexWeight i := by
  cases i <;> rfl

/-- The induced algebra automorphism of the concrete conformal matrix algebra. -/
def conformalTriality : ConformalMatrix ≃ₐ[ℂ] ConformalMatrix :=
  Matrix.reindexAlgEquiv ℂ ℂ conformalIndexTriality

theorem conformalTriality_mem_grade (g : TKKGrade) {A : ConformalMatrix}
    (hA : A ∈ conformalGrade g) :
    conformalTriality A ∈ conformalGrade g := by
  intro r c hrc
  change A (conformalIndexTriality.symm r)
      (conformalIndexTriality.symm c) = 0
  apply hA
  simpa using hrc

theorem zornCoordinates_canonicalTriality (X : Zorn) (i : Fin 8) :
    zornCoordinates (CanonicalZornProjectiveTKKBridge.canonicalTriality X) i =
      zornCoordinates X (trialityCoordinateEquiv.symm i) := by
  fin_cases i <;>
    rfl

theorem conformalTriality_zornPositive (X : Zorn) :
    conformalTriality (zornPositive X) =
      zornPositive (CanonicalZornProjectiveTKKBridge.canonicalTriality X) := by
  ext r c
  cases r <;> cases c <;>
    simp [conformalTriality, Matrix.reindexAlgEquiv, zornPositive,
      conformalIndexTriality, zornCoordinates_canonicalTriality]

theorem conformalTriality_zornNegative (X : Zorn) :
    conformalTriality (zornNegative X) =
      zornNegative (CanonicalZornProjectiveTKKBridge.canonicalTriality X) := by
  ext r c
  cases r <;> cases c <;>
    simp [conformalTriality, Matrix.reindexAlgEquiv, zornNegative,
      conformalIndexTriality, zornCoordinates_canonicalTriality]

theorem conformalTriality_bracket (A B : ConformalMatrix) :
    conformalTriality ⁅A, B⁆ =
      ⁅conformalTriality A, conformalTriality B⁆ := by
  change conformalTriality (A * B - B * A) =
    conformalTriality A * conformalTriality B -
      conformalTriality B * conformalTriality A
  simp

/-- Triality is compatible with the canonical five-graded closure: it
preserves both odd grades, their mixed bracket, and the grade-zero target. -/
theorem canonical_triality_five_grade_covariance (X Y : Zorn) :
    conformalTriality (zornPositive X) ∈ conformalGrade p1 ∧
    conformalTriality (zornNegative Y) ∈ conformalGrade m1 ∧
    conformalTriality ⁅zornNegative Y, zornPositive X⁆ ∈
      conformalGrade z0 := by
  refine ⟨conformalTriality_mem_grade p1 (zornPositive_mem X),
    conformalTriality_mem_grade m1 (zornNegative_mem Y), ?_⟩
  exact conformalTriality_mem_grade z0
    (zorn_mixed_bracket_mem_grade_zero Y X)

/-! ## Affine conformal/projective coordinates on the same `1 ⊕ 8 ⊕ 1` block -/

open ProjectiveAffineConformalClosure55
open CanonicalZornProjectiveTKKBridge

/-- Coordinates of the existing `(5,5)` projective closure on the same
`1 ⊕ 8 ⊕ 1` index type used by the five-graded matrix algebra. -/
def pac55Coordinates (X : PACSplit55) : ConformalIndex → ℝ
  | .minus => X.u
  | .middle i => ![X.x0, X.x1, X.x2, X.x3,
      X.y0, X.y1, X.y2, X.y3] i
  | .plus => X.v

theorem pac55Coordinates_injective : Function.Injective pac55Coordinates := by
  intro X Y h
  cases X
  cases Y
  have hm := congrFun h ConformalIndex.minus
  have hp := congrFun h ConformalIndex.plus
  have h0 := congrFun h (ConformalIndex.middle 0)
  have h1 := congrFun h (ConformalIndex.middle 1)
  have h2 := congrFun h (ConformalIndex.middle 2)
  have h3 := congrFun h (ConformalIndex.middle 3)
  have h4 := congrFun h (ConformalIndex.middle 4)
  have h5 := congrFun h (ConformalIndex.middle 5)
  have h6 := congrFun h (ConformalIndex.middle 6)
  have h7 := congrFun h (ConformalIndex.middle 7)
  simp only [pac55Coordinates] at hm hp h0 h1 h2 h3 h4 h5 h6 h7
  subst_vars
  rfl

/-- Split `(5,5)` quadratic form written on conformal block coordinates. -/
def conformalVectorQuadratic (v : ConformalIndex → ℝ) : ℝ :=
  v (.middle 0)^2 + v (.middle 1)^2 +
    v (.middle 2)^2 + v (.middle 3)^2 + (v .minus)^2 -
    (v (.middle 4)^2 + v (.middle 5)^2 +
      v (.middle 6)^2 + v (.middle 7)^2 + (v .plus)^2)

theorem conformalVectorQuadratic_pac55Coordinates (X : PACSplit55) :
    conformalVectorQuadratic (pac55Coordinates X) = Q55 X := by
  rfl

/-- Projective null-cone coordinates obtained from a real Zorn element. -/
def zornProjectiveVector (X : ZornCore.Zorn) : ConformalIndex → ℝ :=
  pac55Coordinates (zornConformalEmbed X)

theorem zornProjectiveVector_null (X : ZornCore.Zorn) :
    conformalVectorQuadratic (zornProjectiveVector X) = 0 := by
  rw [zornProjectiveVector, conformalVectorQuadratic_pac55Coordinates]
  exact zornConformalEmbed_null X

/-- The carrier, triality, concrete five-grading, and affine projective closure
now meet in one theorem on a single real Zorn input. -/
theorem canonical_triality_five_grade_projective_closure
    (X Y : ZornCore.Zorn) :
    conformalVectorQuadratic (zornProjectiveVector X) = 0 ∧
    zornPositive (coreToCanonical X) ∈ conformalGrade p1 ∧
    zornNegative (coreToCanonical Y) ∈ conformalGrade m1 ∧
    ⁅zornNegative (coreToCanonical Y),
        zornPositive (coreToCanonical X)⁆ ∈ conformalGrade z0 ∧
    conformalTriality (zornPositive (coreToCanonical X)) =
      zornPositive (coreToCanonical (ZornCore.triality X)) := by
  refine ⟨zornProjectiveVector_null X,
    zornPositive_mem _, zornNegative_mem _,
    zorn_mixed_bracket_mem_grade_zero _ _, ?_⟩
  rw [conformalTriality_zornPositive, coreToCanonical_triality]

end CanonicalZornFiveGradedClosure

end noncomputable section
